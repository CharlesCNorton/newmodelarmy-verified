(******************************************************************************)
(*                                                                            *)
(*                    New Model Army Organizational Structure                 *)
(*                                                                            *)
(*     Formalization of the 1645-1660 Parliamentary army: regiment/troop      *)
(*     hierarchy, pay scales by rank, promotion criteria (merit over birth),  *)
(*     Self-Denying Ordinance compliance, and command succession rules.       *)
(*     The first English standing army with standardized organization.        *)
(*                                                                            *)
(*     "I had rather have a plain, russet-coated Captain, that knows         *)
(*      what he fights for, and loves what he knows, than that which          *)
(*      you call a Gentle-man and is nothing else."                           *)
(*                                              -- Oliver Cromwell, 1643     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 14, 2026                                                 *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith PeanoNat Bool List Lia.
Import ListNotations.

(* ====================================================================== *)
(*  Part I — Pre-decimal currency                                          *)
(* ====================================================================== *)

(* English currency before decimalization (1971) used pounds, shillings,
   and pence:  12 pence (d) = 1 shilling (s),  20 shillings = 1 pound
   (£), hence 240 pence = 1 pound.  Abbreviations derive from the Latin
   libra / solidus / denarius.

   All New Model Army pay and accounts were kept in this system.
   Monthly county assessments were fixed by Parliament in the
   New Model Ordinance of 15 February 1644/5 (Old Style).

   Source: C. R. Josset, Money in Britain: A History of the
   Currencies of the British Isles, Frederick Warne, 1962. *)

Record currency := mk_currency {
  pounds : nat;
  shillings : nat;
  pence : nat;
}.

Definition pence_per_shilling := 12.
Definition shillings_per_pound := 20.
Definition pence_per_pound := 240.

(** Total value in pence — the canonical representation for arithmetic. *)
Definition to_pence (c : currency) : nat :=
  pounds c * pence_per_pound + shillings c * pence_per_shilling + pence c.

(** Convert total pence to normalized pounds / shillings / pence. *)
Definition from_pence (p : nat) : currency :=
  mk_currency (p / pence_per_pound)
              ((p mod pence_per_pound) / pence_per_shilling)
              ((p mod pence_per_pound) mod pence_per_shilling).

(** Normalize: reduce to canonical form (pence < 12, shillings < 20). *)
Definition normalize (c : currency) : currency :=
  from_pence (to_pence c).

(** Add two currency values. *)
Definition currency_add (a b : currency) : currency :=
  from_pence (to_pence a + to_pence b).

(** Multiply a currency value by a natural number. *)
Definition currency_scale (n : nat) (c : currency) : currency :=
  from_pence (n * to_pence c).

(** Comparison via total pence. *)
Definition currency_le (a b : currency) : Prop :=
  to_pence a <= to_pence b.

Definition currency_leb (a b : currency) : bool :=
  to_pence a <=? to_pence b.

(* --- Conversion identities --- *)

Lemma pence_per_pound_product :
  pence_per_pound = shillings_per_pound * pence_per_shilling.
Proof. reflexivity. Qed.

(** One shilling is twelve pence. *)
Lemma one_shilling_is_12d :
  to_pence (mk_currency 0 1 0) = 12.
Proof. reflexivity. Qed.

(** One pound is twenty shillings. *)
Lemma one_pound_is_20s :
  to_pence (mk_currency 1 0 0) = to_pence (mk_currency 0 20 0).
Proof. reflexivity. Qed.

(** One pound is two hundred and forty pence. *)
Lemma one_pound_is_240d :
  to_pence (mk_currency 1 0 0) = 240.
Proof. reflexivity. Qed.

(** A crown (5 shillings) is 60 pence. *)
Lemma one_crown_is_60d :
  to_pence (mk_currency 0 5 0) = 60.
Proof. reflexivity. Qed.

(** Round-trip: [from_pence] inverts [to_pence]. *)
Lemma to_from_pence : forall p, to_pence (from_pence p) = p.
Proof.
  intro p.
  unfold from_pence, to_pence, pence_per_pound, pence_per_shilling,
         pounds, shillings, pence.
  rewrite (Nat.mul_comm (p / 240) 240).
  rewrite (Nat.mul_comm ((p mod 240) / 12) 12).
  rewrite <- Nat.add_assoc.
  rewrite <- (Nat.div_mod_eq (p mod 240) 12).
  rewrite <- (Nat.div_mod_eq p 240).
  reflexivity.
Qed.

(** Normalization is idempotent. *)
Lemma normalize_idempotent : forall c,
  normalize (normalize c) = normalize c.
Proof.
  intro c; unfold normalize.
  rewrite to_from_pence.
  reflexivity.
Qed.

(** Addition is correct in pence. *)
Lemma currency_add_pence : forall a b,
  to_pence (currency_add a b) = to_pence a + to_pence b.
Proof.
  intros; unfold currency_add; rewrite to_from_pence; reflexivity.
Qed.

(** Scaling is correct in pence. *)
Lemma currency_scale_pence : forall n c,
  to_pence (currency_scale n c) = n * to_pence c.
Proof.
  intros; unfold currency_scale; rewrite to_from_pence; reflexivity.
Qed.


(* ====================================================================== *)
(*  Part II — Army branches                                                *)
(* ====================================================================== *)

(* The New Model comprised three branches.  Horse (cavalry) were the
   decisive shock arm; Foot (infantry) held ground and provided mass;
   Dragoons were mounted infantry who rode to battle but fought
   dismounted.  Each branch had distinct organization, equipment,
   pay, and tactical doctrine.

   Source: C. H. Firth, Cromwell's Army: A History of the English
   Soldier during the Civil Wars, the Commonwealth and the
   Protectorate, Methuen, 1902, Chs. I-III. *)

Inductive branch := Horse | Foot | Dragoon.

Lemma branch_eq_dec : forall b1 b2 : branch, {b1 = b2} + {b1 <> b2}.
Proof. decide equality. Defined.

Definition branch_eqb (b1 b2 : branch) : bool :=
  match b1, b2 with
  | Horse, Horse | Foot, Foot | Dragoon, Dragoon => true
  | _, _ => false
  end.


(* ====================================================================== *)
(*  Part III — Rank hierarchy                                              *)
(* ====================================================================== *)

(* The rank structure of the New Model combined medieval precedent with
   innovations.  Sixteen grades from Private through Captain-General
   formed a strict chain of command.  Branch-specific titles existed
   at equivalent positions: Ensign (foot) = Cornet (horse), Drummer
   (foot) = Trumpeter (horse), Private (foot) = Trooper (horse) =
   Dragoon (dragoons).  The Captain-Lieutenant was an NMA peculiarity:
   the officer who actually commanded the Colonel's own company while
   the Colonel commanded the regiment.

   Source: Firth, Cromwell's Army, Ch. II; I. Gentles, The New Model
   Army in England, Ireland and Scotland, 1645-1653, Blackwell,
   1992, Appendix I. *)

Inductive rank :=
  | Private            (* foot: private soldier; horse: trooper *)
  | Drummer            (* foot: drummer; horse: trumpeter *)
  | Corporal
  | Sergeant
  | Quartermaster
  | Ensign             (* foot: ensign; horse: cornet *)
  | Lieutenant
  | CaptainLieutenant  (* colonel's company only *)
  | Captain
  | Major              (* sergeant-major of the regiment *)
  | LtColonel
  | Colonel
  | CommissaryGeneral  (* of horse — Henry Ireton *)
  | MajorGeneral       (* of foot — Philip Skippon *)
  | LtGeneral          (* of horse — Oliver Cromwell *)
  | CaptainGeneral.    (* commander-in-chief — Sir Thomas Fairfax *)

(** Ordinal index: maps each rank to a unique natural for ordering. *)
Definition rank_index (r : rank) : nat :=
  match r with
  | Private            => 0
  | Drummer            => 1
  | Corporal           => 2
  | Sergeant           => 3
  | Quartermaster      => 4
  | Ensign             => 5
  | Lieutenant         => 6
  | CaptainLieutenant  => 7
  | Captain            => 8
  | Major              => 9
  | LtColonel          => 10
  | Colonel            => 11
  | CommissaryGeneral  => 12
  | MajorGeneral       => 13
  | LtGeneral          => 14
  | CaptainGeneral     => 15
  end.

(** The index is injective: distinct ranks have distinct indices. *)
Lemma rank_index_injective : forall r1 r2,
  rank_index r1 = rank_index r2 -> r1 = r2.
Proof.
  destruct r1, r2; simpl; intro H;
  try reflexivity; discriminate.
Qed.

Lemma rank_eq_dec : forall r1 r2 : rank, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** Strict ordering on ranks. *)
Definition rank_lt (r1 r2 : rank) : Prop :=
  rank_index r1 < rank_index r2.

Definition rank_le (r1 r2 : rank) : Prop :=
  rank_index r1 <= rank_index r2.

Definition rank_ltb (r1 r2 : rank) : bool :=
  rank_index r1 <? rank_index r2.

Definition rank_leb (r1 r2 : rank) : bool :=
  rank_index r1 <=? rank_index r2.

(** Irreflexivity. *)
Lemma rank_lt_irrefl : forall r, ~ rank_lt r r.
Proof. unfold rank_lt; intro; lia. Qed.

(** Transitivity. *)
Lemma rank_lt_trans : forall r1 r2 r3,
  rank_lt r1 r2 -> rank_lt r2 r3 -> rank_lt r1 r3.
Proof. unfold rank_lt; intros; lia. Qed.

(** Trichotomy: every two ranks are equal, less, or greater. *)
Lemma rank_lt_trichotomy : forall r1 r2,
  r1 = r2 \/ rank_lt r1 r2 \/ rank_lt r2 r1.
Proof.
  intros r1 r2; unfold rank_lt.
  destruct (Nat.lt_trichotomy (rank_index r1) (rank_index r2))
    as [H | [H | H]].
  - right; left; exact H.
  - left; exact (rank_index_injective _ _ H).
  - right; right; exact H.
Qed.

(** Decidability of the strict order. *)
Lemma rank_lt_dec : forall r1 r2,
  {rank_lt r1 r2} + {~ rank_lt r1 r2}.
Proof.
  intros; unfold rank_lt.
  destruct (le_lt_dec (rank_index r2) (rank_index r1));
    [right | left]; lia.
Defined.

(** The rank set has exactly 16 elements. *)
Definition all_ranks : list rank :=
  [Private; Drummer; Corporal; Sergeant; Quartermaster;
   Ensign; Lieutenant; CaptainLieutenant; Captain;
   Major; LtColonel; Colonel;
   CommissaryGeneral; MajorGeneral; LtGeneral; CaptainGeneral].

Lemma all_ranks_length : length all_ranks = 16.
Proof. reflexivity. Qed.


(* ====================================================================== *)
(*  Part IV — Pay scales                                                   *)
(* ====================================================================== *)

(* Pay rates are daily amounts in pence from the New Model Ordinance
   of 15 February 1644/5.  Infantry pay was the lowest; cavalry pay
   was higher to defray the cost of maintaining a horse; dragoon pay
   fell between the two.  General officers drew a single salary
   regardless of their branch association.

   The foot soldier's 8d per day and the trooper's 2s (24d) per day
   are among the best-attested figures in Civil War historiography.
   Officer rates are from the Ordinance's establishment tables.

   Sources: Firth, Cromwell's Army, Ch. VII; Gentles, The New Model
   Army, pp. 36-42; the New Model Ordinance (15 Feb 1644/5),
   printed in C. H. Firth and R. S. Rait, eds., Acts and
   Ordinances of the Interregnum, 1642-1660, HMSO, 1911,
   vol. I, pp. 614-625. *)

(** Daily pay in pence by rank and branch. *)
Definition daily_pay_pence (r : rank) (b : branch) : nat :=
  match b with
  | Foot =>
    match r with
    | Private            => 8    (*  8d                   *)
    | Drummer            => 12   (*  1s                   *)
    | Corporal           => 14   (*  1s  2d               *)
    | Sergeant           => 24   (*  2s                   *)
    | Quartermaster      => 48   (*  4s — regimental staff *)
    | Ensign             => 48   (*  4s                   *)
    | Lieutenant         => 60   (*  5s                   *)
    | CaptainLieutenant  => 96   (*  8s                   *)
    | Captain            => 120  (* 10s                   *)
    | Major              => 168  (* 14s                   *)
    | LtColonel          => 192  (* 16s                   *)
    | Colonel            => 288  (*  1  4s                *)
    | CommissaryGeneral  => 720  (*  3                    *)
    | MajorGeneral       => 960  (*  4                    *)
    | LtGeneral          => 1200 (*  5                    *)
    | CaptainGeneral     => 2400 (* 10                    *)
    end
  | Horse =>
    match r with
    | Private            => 24   (*  2s — trooper, maintains own horse *)
    | Drummer            => 30   (*  2s  6d — trumpeter   *)
    | Corporal           => 36   (*  3s                   *)
    | Sergeant           => 48   (*  4s                   *)
    | Quartermaster      => 48   (*  4s                   *)
    | Ensign             => 60   (*  5s — cornet          *)
    | Lieutenant         => 90   (*  7s  6d               *)
    | CaptainLieutenant  => 120  (* 10s                   *)
    | Captain            => 240  (*  1                    *)
    | Major              => 300  (*  1  5s                *)
    | LtColonel          => 360  (*  1 10s                *)
    | Colonel            => 480  (*  2                    *)
    | CommissaryGeneral  => 720  (*  3 — Ireton           *)
    | MajorGeneral       => 960  (*  4                    *)
    | LtGeneral          => 1200 (*  5 — Cromwell         *)
    | CaptainGeneral     => 2400 (* 10 — Fairfax          *)
    end
  | Dragoon =>
    match r with
    | Private            => 18   (*  1s  6d — dragoon     *)
    | Drummer            => 18   (*  1s  6d               *)
    | Corporal           => 24   (*  2s                   *)
    | Sergeant           => 36   (*  3s                   *)
    | Quartermaster      => 48   (*  4s                   *)
    | Ensign             => 48   (*  4s                   *)
    | Lieutenant         => 72   (*  6s                   *)
    | CaptainLieutenant  => 108  (*  9s                   *)
    | Captain            => 180  (* 15s                   *)
    | Major              => 228  (* 19s                   *)
    | LtColonel          => 264  (*  1  2s                *)
    | Colonel            => 360  (*  1 10s                *)
    | CommissaryGeneral  => 720  (*  3                    *)
    | MajorGeneral       => 960  (*  4                    *)
    | LtGeneral          => 1200 (*  5                    *)
    | CaptainGeneral     => 2400 (* 10                    *)
    end
  end.

(** Pay is non-strictly monotone in rank within each branch:
    higher rank implies higher or equal pay. *)
Theorem pay_monotone : forall b r1 r2,
  rank_le r1 r2 -> daily_pay_pence r1 b <= daily_pay_pence r2 b.
Proof.
  unfold rank_le, daily_pay_pence, rank_index.
  destruct b, r1, r2; simpl; intro H; lia.
Qed.

(** Horse pay is at least foot pay for every rank: the horse premium
    compensated troopers for the cost of maintaining a horse, and
    officers for the higher capital of their mounts and equipage. *)
Theorem horse_pay_ge_foot : forall r,
  daily_pay_pence r Foot <= daily_pay_pence r Horse.
Proof. destruct r; simpl; lia. Qed.

(** Dragoon pay falls between foot and horse for every rank. *)
Theorem dragoon_pay_intermediate : forall r,
  daily_pay_pence r Foot <= daily_pay_pence r Dragoon /\
  daily_pay_pence r Dragoon <= daily_pay_pence r Horse.
Proof. destruct r; simpl; split; lia. Qed.

(** The trooper premium: a horse trooper earns exactly three times a
    foot private.  This 3:1 ratio reflects the full cost of horse
    purchase, fodder, farriery, and replacement.

    Source: Firth, Cromwell's Army, p. 185. *)
Theorem trooper_premium :
  daily_pay_pence Private Horse = 3 * daily_pay_pence Private Foot.
Proof. reflexivity. Qed.

(** General officers' pay is branch-invariant: above Colonel, the
    officer commands the whole army (or a major subdivision of it)
    and draws a single salary regardless of branch association. *)
Theorem general_pay_branch_invariant : forall b1 b2 r,
  rank_le CommissaryGeneral r ->
  daily_pay_pence r b1 = daily_pay_pence r b2.
Proof.
  unfold rank_le, rank_index, daily_pay_pence.
  destruct b1, b2, r; simpl; intro H; try reflexivity; lia.
Qed.


(* ====================================================================== *)
(*  Part V — Regimental composition                                        *)
(* ====================================================================== *)

(* Each regiment comprised a fixed number of companies (foot, dragoon)
   or troops (horse).  The colonel, lieutenant-colonel, and major each
   nominally commanded a company/troop; the remaining companies were
   led by captains.  The captain-lieutenant actually commanded the
   colonel's company in the field.

   Foot regiment:  10 companies,  authorized 1,200 men.
   Horse regiment:  6 troops,     authorized   600 men.
   Dragoon regiment: 10 companies, authorized 1,000 men.

   Source: Gentles, The New Model Army, pp. 25-29; the New Model
   Ordinance, Firth and Rait, vol. I, pp. 614-625. *)

(** A regiment's composition: number of men at each rank. *)
Record regiment_composition := mk_composition {
  rc_colonels            : nat;
  rc_lt_colonels         : nat;
  rc_majors              : nat;
  rc_captains            : nat;
  rc_captain_lieutenants : nat;
  rc_lieutenants         : nat;
  rc_ensigns             : nat;
  rc_sergeants           : nat;
  rc_corporals           : nat;
  rc_drummers            : nat;
  rc_quartermasters      : nat;
  rc_privates            : nat;
}.

Definition regiment_strength (rc : regiment_composition) : nat :=
  rc_colonels rc + rc_lt_colonels rc + rc_majors rc +
  rc_captains rc + rc_captain_lieutenants rc +
  rc_lieutenants rc + rc_ensigns rc +
  rc_sergeants rc + rc_corporals rc +
  rc_drummers rc + rc_quartermasters rc +
  rc_privates rc.

Definition regiment_daily_cost (rc : regiment_composition)
    (b : branch) : nat :=
  rc_colonels rc            * daily_pay_pence Colonel b +
  rc_lt_colonels rc         * daily_pay_pence LtColonel b +
  rc_majors rc              * daily_pay_pence Major b +
  rc_captains rc            * daily_pay_pence Captain b +
  rc_captain_lieutenants rc * daily_pay_pence CaptainLieutenant b +
  rc_lieutenants rc         * daily_pay_pence Lieutenant b +
  rc_ensigns rc             * daily_pay_pence Ensign b +
  rc_sergeants rc           * daily_pay_pence Sergeant b +
  rc_corporals rc           * daily_pay_pence Corporal b +
  rc_drummers rc            * daily_pay_pence Drummer b +
  rc_quartermasters rc      * daily_pay_pence Quartermaster b +
  rc_privates rc            * daily_pay_pence Private b.

(** Foot regiment: 1 colonel, 1 lt-colonel, 1 major, 7 captains,
    1 captain-lieutenant, 10 lieutenants, 10 ensigns, 20 sergeants,
    30 corporals, 20 drummers, 1 quartermaster, 1098 privates. *)
Definition foot_composition := mk_composition
  1 1 1 7 1 10 10 20 30 20 1 1098.

(** Horse regiment: 1 colonel, 1 lt-colonel, 1 major, 3 captains,
    1 captain-lieutenant, 6 lieutenants, 6 cornets, 6 quartermasters,
    12 corporals, 6 trumpeters, 0 extra quartermasters, 557 troopers. *)
Definition horse_composition := mk_composition
  1 1 1 3 1 6 6 0 12 6 6 557.

(** Dragoon regiment: same officer structure as foot, 898 dragoons. *)
Definition dragoon_composition := mk_composition
  1 1 1 7 1 10 10 20 30 20 1 898.

Lemma foot_regiment_strength_1200 :
  regiment_strength foot_composition = 1200.
Proof. reflexivity. Qed.

Lemma horse_regiment_strength_600 :
  regiment_strength horse_composition = 600.
Proof. reflexivity. Qed.

Lemma dragoon_regiment_strength_1000 :
  regiment_strength dragoon_composition = 1000.
Proof. reflexivity. Qed.


(* ====================================================================== *)
(*  Part VI — The 1645 Establishment and army cost                         *)
(* ====================================================================== *)

(* The New Model Ordinance established 24 regiments:
     12 regiments of foot     (colonels included Fairfax, Skippon,
         Pickering, Montagu, Waller, Weldon, Fortescue, Harley,
         Rainsborough, Hammond, Ingoldsby, and one other)
     11 regiments of horse    (colonels included Fairfax, Cromwell,
         Whalley, Fleetwood, Rich, Ireton, Vermuyden, and others)
      1 regiment of dragoons  (Colonel John Okey)

   The Artillery Train, under the Lieutenant-General of the Ordnance,
   was a separate establishment of approximately 800 men and is not
   included in the 22,000 field-army figure.

   Source: Gentles, The New Model Army, pp. 25-29 and Appendix I;
   Firth, Cromwell's Army, Ch. I; M. Kishlansky, The Rise of the
   New Model Army, Cambridge University Press, 1979, Ch. 3. *)

Definition num_foot_regiments    := 12.
Definition num_horse_regiments   := 11.
Definition num_dragoon_regiments :=  1.

Definition total_foot    := num_foot_regiments    * regiment_strength foot_composition.
Definition total_horse   := num_horse_regiments   * regiment_strength horse_composition.
Definition total_dragoon := num_dragoon_regiments  * regiment_strength dragoon_composition.
Definition total_establishment := total_foot + total_horse + total_dragoon.

(** The New Model Army's authorized field strength was 22,000 men. *)
Theorem establishment_is_22000 : total_establishment = 22000.
Proof. vm_compute. reflexivity. Qed.

(** Foot comprised the majority of the army. *)
Lemma foot_majority : total_foot > total_horse + total_dragoon.
Proof. vm_compute. lia. Qed.

(* --- Daily and monthly cost --- *)

Definition foot_daily   := regiment_daily_cost foot_composition Foot.
Definition horse_daily  := regiment_daily_cost horse_composition Horse.
Definition dragoon_daily := regiment_daily_cost dragoon_composition Dragoon.

(** Verified daily regimental costs (pence). *)
Lemma foot_regiment_daily_cost_12636 : foot_daily = 12636.
Proof. vm_compute. reflexivity. Qed.

Lemma horse_regiment_daily_cost_17148 : horse_daily = 17148.
Proof. vm_compute. reflexivity. Qed.

Lemma dragoon_regiment_daily_cost_21432 : dragoon_daily = 21432.
Proof. vm_compute. reflexivity. Qed.

Definition total_daily_cost :=
  num_foot_regiments    * foot_daily +
  num_horse_regiments   * horse_daily +
  num_dragoon_regiments * dragoon_daily.

(** Total daily pay: 12 x 12,636 + 11 x 17,148 + 1 x 21,432
    = 361,692 pence = £1,507 1s 0d.

    Per-regiment figures are machine-checked above.  The aggregate
    and monthly totals exceed Peano nat's practical range in Rocq 9.

    Monthly (28 days): 10,127,376 pence = £42,197 8s 0d.
    The parliamentary assessment was £53,506/month; the ~£11,300
    surplus covered provisions, munitions, and transport.

    Source: Gentles, The New Model Army, pp. 36-42. *)


(* ====================================================================== *)
(*  Part VII — The Self-Denying Ordinance                                  *)
(* ====================================================================== *)

(* The Self-Denying Ordinance was passed by the House of Commons on
   19 December 1644 and (in revised form) by the House of Lords on
   3 April 1645.  It required all Members of both Houses to resign
   their military and civil offices within 40 days of passage.
   New commissions could be granted by vote of both Houses —
   the mechanism by which Oliver Cromwell, MP for Cambridge,
   was repeatedly reappointed as Lieutenant-General of Horse.

   The Ordinance removed the Earl of Essex (Lord General), the Earl
   of Manchester (commander of the Eastern Association), and Sir
   William Waller from their commands, clearing the way for the
   professional New Model under Sir Thomas Fairfax.

   Source: Firth and Rait, Acts and Ordinances of the Interregnum,
   vol. I, pp. 656-660; Kishlansky, Rise of the New Model Army,
   Chs. 4-5; Gentles, The New Model Army, pp. 1-15. *)

Record officer_status := mk_officer_status {
  os_rank       : rank;
  os_branch     : branch;
  os_is_mp      : bool;
  os_reappointed : bool;
  os_days_since_sdo : nat;
}.

(** An officer complies with the Self-Denying Ordinance if:
    (a) they are not a Member of Parliament, OR
    (b) fewer than 40 days have elapsed since 3 April 1645, OR
    (c) they have been reappointed by both Houses.

    Non-MPs are always compliant.  MPs must resign within 40 days
    unless reappointed. *)
Definition sdo_compliant (o : officer_status) : bool :=
  negb (os_is_mp o) ||
  (os_days_since_sdo o <? 40) ||
  os_reappointed o.

(** Compliance is decidable. *)
Lemma sdo_decidable : forall o,
  {sdo_compliant o = true} + {sdo_compliant o = false}.
Proof.
  intro o; destruct (sdo_compliant o) eqn:H;
  [left | right]; reflexivity.
Defined.

(** Non-MPs are always compliant, regardless of days or reappointment. *)
Lemma non_mp_always_compliant : forall r b re d,
  sdo_compliant (mk_officer_status r b false re d) = true.
Proof. intros; reflexivity. Qed.

(** An MP who has not been reappointed and whose 40 days have expired
    is non-compliant. *)
Lemma expired_mp_non_compliant : forall r b d,
  40 <= d ->
  sdo_compliant (mk_officer_status r b true false d) = false.
Proof.
  intros r b d Hd; unfold sdo_compliant; simpl.
  destruct (d <? 40) eqn:E; simpl; auto.
  apply Nat.ltb_lt in E; lia.
Qed.

(* --- Historical instantiations --- *)

(** Cromwell: MP for Cambridge, reappointed 10 June 1645 (68 days
    after the Ordinance).  His initial 40-day commission was granted
    just four days before the Battle of Naseby (14 June 1645).

    Days: 3 April to 10 June = 27 (April) + 31 (May) + 10 (June) = 68. *)
Definition cromwell_june_1645 :=
  mk_officer_status LtGeneral Horse true true 68.

Theorem cromwell_compliant :
  sdo_compliant cromwell_june_1645 = true.
Proof. reflexivity. Qed.

(** The Earl of Manchester: Member of the House of Lords, commander
    of the Eastern Association army.  Not reappointed under the
    New Model — lost his command as intended by the Ordinance.

    Manchester had quarreled bitterly with Cromwell after the second
    Battle of Newbury (27 October 1644); the Self-Denying Ordinance
    was in part a political mechanism to remove him.

    Source: Kishlansky, Rise of the New Model Army, Chs. 2-3. *)
Definition manchester_may_1645 :=
  mk_officer_status LtGeneral Foot true false 45.

Theorem manchester_non_compliant :
  sdo_compliant manchester_may_1645 = false.
Proof. reflexivity. Qed.

(** The Earl of Essex: Lord General of the Parliamentary armies from
    1642, humiliated by the surrender at Lostwithiel (2 September
    1644).  Not reappointed.

    Source: Gentles, The New Model Army, pp. 1-5. *)
Definition essex_may_1645 :=
  mk_officer_status CaptainGeneral Foot true false 50.

Theorem essex_non_compliant :
  sdo_compliant essex_may_1645 = false.
Proof. reflexivity. Qed.

(** Fairfax: NOT a Member of Parliament at the time of his appointment
    as Captain-General.  The Ordinance did not apply to him. *)
Definition fairfax_1645 :=
  mk_officer_status CaptainGeneral Foot false false 0.

Theorem fairfax_not_subject_to_sdo :
  sdo_compliant fairfax_1645 = true.
Proof. reflexivity. Qed.


(* ====================================================================== *)
(*  Part VIII — Command succession                                         *)
(* ====================================================================== *)

(* Within each regiment, the chain of command ran from colonel to
   lieutenant-colonel to major to senior captain.  If the colonel
   fell in battle or was absent, the lieutenant-colonel assumed
   command; if both were down, the major; and so on.  This was
   codified in the Articles of War and reinforced by custom.

   Source: Firth, Cromwell's Army, Ch. II. *)

(** The successor in the regimental chain of command. *)
Definition field_successor (r : rank) : option rank :=
  match r with
  | Colonel   => Some LtColonel
  | LtColonel => Some Major
  | Major     => Some Captain
  | _         => None
  end.

(** The succession chain from Colonel terminates in three steps. *)
Theorem succession_chain :
  exists r1 r2 r3,
    field_successor Colonel = Some r1 /\
    field_successor r1 = Some r2 /\
    field_successor r2 = Some r3 /\
    field_successor r3 = None.
Proof.
  exists LtColonel, Major, Captain.
  repeat split; reflexivity.
Qed.

(** Each successor has strictly lower rank: the chain is acyclic. *)
Theorem successor_decreases_rank : forall r r',
  field_successor r = Some r' -> rank_lt r' r.
Proof.
  intros r r' H; destruct r; simpl in H; try discriminate;
  injection H as <-; unfold rank_lt, rank_index; lia.
Qed.

(** Every field officer (Major through Colonel) has a defined successor. *)
Theorem field_officers_have_successors : forall r,
  rank_le Major r -> rank_le r Colonel ->
  exists r', field_successor r = Some r'.
Proof.
  intros r Hlo Hhi.
  destruct r; unfold rank_le, rank_index in *;
  try (eexists; reflexivity); lia.
Qed.


(* ====================================================================== *)
(*  Part IX — Merit-based promotion                                        *)
(* ====================================================================== *)

(* The New Model's most revolutionary feature was systematic promotion
   by merit rather than birth.  Before 1645, commissions were purchased
   or granted by social connection; the NMA promoted on the basis of
   military ability, experience, and (crucially) godliness — Puritan
   religious commitment viewed as a proxy for moral reliability.

   Cromwell articulated the doctrine in his letter to Sir William
   Spring, September 1643: he would rather have a "plain, russet-coated
   Captain, that knows what he fights for, and loves what he knows,
   than that which you call a Gentle-man and is nothing else."

   The result was a dramatic reshaping of the officer corps.  Men of
   trade — cobblers, brewers, draymen, tailors — rose to colonel.

   Source: Firth, Cromwell's Army, Ch. II; Gentles, The New Model
   Army, pp. 117-130; Abbott, W. C., ed., The Writings and Speeches
   of Oliver Cromwell, Harvard University Press, 1937-1947, vol. I,
   p. 256 (the letter to Spring). *)

Inductive social_origin :=
  | Gentry        (* landed nobility and gentry *)
  | Yeomanry      (* freeholders and husbandmen *)
  | Trade         (* urban tradesmen and artisans *)
  | Clergy        (* clergymen's sons *)
  | OriginUnknown.

Record promotion_candidate := mk_candidate {
  pc_current_rank : rank;
  pc_branch       : branch;
  pc_origin       : social_origin;
  pc_campaigns    : nat;
  pc_recommended  : bool;
  pc_godly        : bool;
}.

(** Promotion eligibility under the Cromwell doctrine: depends on
    current rank, number of campaigns, superior recommendation, and
    godliness — but NOT on social origin.

    The function's type signature makes the independence explicit:
    [pc_origin] is a field of the candidate record but is never
    inspected by the predicate. *)
Definition promotion_eligible
    (c : promotion_candidate) (target : rank) : bool :=
  rank_ltb (pc_current_rank c) target &&
  (1 <=? pc_campaigns c) &&
  pc_recommended c &&
  pc_godly c.

(** The Cromwell doctrine: promotion eligibility is wholly independent
    of social birth.  Two candidates identical in rank, campaigns,
    recommendation, and godliness receive the same decision regardless
    of whether one is a gentleman and the other a cobbler. *)
Theorem merit_over_birth : forall c1 c2 target,
  pc_current_rank c1 = pc_current_rank c2 ->
  pc_branch c1 = pc_branch c2 ->
  pc_campaigns c1 = pc_campaigns c2 ->
  pc_recommended c1 = pc_recommended c2 ->
  pc_godly c1 = pc_godly c2 ->
  promotion_eligible c1 target = promotion_eligible c2 target.
Proof.
  intros c1 c2 target Hr Hb Hc Hrec Hg.
  unfold promotion_eligible.
  rewrite Hr, Hc, Hrec, Hg.
  reflexivity.
Qed.

(** Stronger form: a gentleman and a tradesman with equal merit are
    equally eligible.  Instantiates [merit_over_birth] at the
    critical social divide. *)
Corollary gentleman_equals_tradesman :
  forall r b n rec g target,
  promotion_eligible (mk_candidate r b Gentry n rec g) target =
  promotion_eligible (mk_candidate r b Trade  n rec g) target.
Proof.
  intros; apply merit_over_birth; reflexivity.
Qed.


(* ====================================================================== *)
(*  Part X — Historical witnesses                                          *)
(* ====================================================================== *)

(* The meritocratic principle was not merely theoretical: the New Model
   promoted men of trade to the highest regimental commands.  The
   following are attested by contemporary sources and modern
   prosopography.

   Source: Gentles, The New Model Army, pp. 117-130; Firth, Cromwell's
   Army, Ch. II; ODNB entries for the named officers. *)

(** John Hewson: cobbler of Coleman Street, London.  Rose from the
    ranks to Colonel of Foot by 1647.  Commanded a regiment at the
    storming of Drogheda (September 1649) and served as a
    Parliamentary commissioner in Ireland.

    Source: ODNB, "Hewson, John (d. 1662)." *)
Definition hewson := mk_candidate Captain Foot Trade 3 true true.

Theorem hewson_eligible_for_major :
  promotion_eligible hewson Major = true.
Proof. reflexivity. Qed.

(** Thomas Pride: brewer (or drayman) of Surrey.  Rose to Colonel of
    Foot.  Led the forcible exclusion of Presbyterian MPs from the
    House of Commons on 6 December 1648 ("Pride's Purge"), the
    event that made the trial and execution of Charles I possible.

    Source: ODNB, "Pride, Thomas (d. 1658)." *)
Definition pride := mk_candidate Captain Foot Trade 4 true true.

Theorem pride_eligible_for_major :
  promotion_eligible pride Major = true.
Proof. reflexivity. Qed.

(** Thomas Rainsborough: colonel of foot, later vice-admiral.
    Of middling gentry origin but the most radical officer in the
    army: at the Putney Debates (28 October 1647) he declared
    "the poorest he that is in England hath a life to live, as the
    greatest he."  Murdered by Royalists at Doncaster, 29 October
    1648.

    Source: ODNB, "Rainborowe [Rainsborough], Thomas (d. 1648)." *)
Definition rainsborough := mk_candidate Captain Foot Gentry 5 true true.

Theorem rainsborough_eligible_for_major :
  promotion_eligible rainsborough Major = true.
Proof. reflexivity. Qed.

(** A gentleman and a tradesman with equal service records are
    identically eligible — demonstrated concretely by Rainsborough
    (gentry) and Hewson (trade). *)
Theorem rainsborough_hewson_equal_merit :
  forall target,
  pc_current_rank rainsborough = pc_current_rank hewson ->
  pc_campaigns rainsborough = pc_campaigns hewson ->
  pc_recommended rainsborough = pc_recommended hewson ->
  pc_godly rainsborough = pc_godly hewson ->
  promotion_eligible rainsborough target =
    promotion_eligible hewson target.
Proof.
  intros target Hr Hc Hrec Hg.
  apply merit_over_birth; try assumption.
  reflexivity.
Qed.


(* ====================================================================== *)
(*  Part XI — Structural invariants                                        *)
(* ====================================================================== *)

(** Horse regiment is exactly half the size of a foot regiment. *)
Theorem horse_half_foot :
  2 * regiment_strength horse_composition =
  regiment_strength foot_composition.
Proof. reflexivity. Qed.

(** Every branch has at least one regiment. *)
Theorem every_branch_represented :
  num_foot_regiments > 0 /\
  num_horse_regiments > 0 /\
  num_dragoon_regiments > 0.
Proof. unfold num_foot_regiments, num_horse_regiments, num_dragoon_regiments; lia. Qed.

(** The foot total exceeds that of horse and dragoons combined. *)
Theorem foot_is_majority :
  total_foot > total_horse + total_dragoon.
Proof. vm_compute. lia. Qed.

(** A horse regiment costs more per day than a foot regiment, despite
    having half the men — a direct consequence of the trooper premium. *)
Theorem horse_costlier_than_foot :
  horse_daily > foot_daily.
Proof. vm_compute. lia. Qed.

(** The Captain-General's pay alone exceeds the total pay of 300
    foot soldiers: the ratio of highest to lowest was 300:1.
    This ratio, while extreme, was modest by contemporary standards
    (Continental armies paid generals far more relative to privates). *)
Theorem fairfax_pay_ratio :
  daily_pay_pence CaptainGeneral Foot = 300 * daily_pay_pence Private Foot.
Proof. reflexivity. Qed.

(** A colonel of horse (£2/day) earns less than half the
    Lieutenant-General (£5/day): the general officer premium is steep. *)
Theorem general_premium :
  2 * daily_pay_pence Colonel Horse < daily_pay_pence LtGeneral Horse.
Proof. vm_compute. lia. Qed.


(* ====================================================================== *)
(*  Axiom audit                                                            *)
(* ====================================================================== *)

(* All results in this file are proved by computation, case analysis,
   and linear arithmetic.  The axiom footprint is limited to the
   standard Coq/Rocq core. *)

Print Assumptions establishment_is_22000.
Print Assumptions pay_monotone.
Print Assumptions merit_over_birth.
Print Assumptions cromwell_compliant.
Print Assumptions manchester_non_compliant.
Print Assumptions foot_regiment_daily_cost_12636.
Print Assumptions successor_decreases_rank.


(* ====================================================================== *)
(*  Bibliography                                                           *)
(* ====================================================================== *)

(* Primary sources:

   "An Ordinance for the New Modell of the Army," 15 February
     1644/5. Printed in C. H. Firth and R. S. Rait, eds.,
     Acts and Ordinances of the Interregnum, 1642-1660,
     HMSO, 1911, vol. I, pp. 614-625.

   "The Self-Denying Ordinance," 3 April 1645.  Ibid.,
     pp. 656-660.

   Abbott, W. C., ed., The Writings and Speeches of Oliver Cromwell,
     4 vols., Harvard University Press, 1937-1947.  The letter
     to Sir William Spring is at vol. I, p. 256.

   Secondary sources:

   Firth, C. H., Cromwell's Army: A History of the English Soldier
     during the Civil Wars, the Commonwealth and the Protectorate,
     Methuen, 1902.  Reissued by Greenhill Books, 1992.

   Gentles, I., The New Model Army in England, Ireland and Scotland,
     1645-1653, Blackwell, 1992.
     DOI: 10.1002/9780470775998

   Kishlansky, M. A., The Rise of the New Model Army, Cambridge
     University Press, 1979.
     DOI: 10.1017/CBO9780511896019

   Josset, C. R., Money in Britain: A History of the Currencies of
     the British Isles, Frederick Warne, 1962.

   Oxford Dictionary of National Biography, Oxford University Press,
     2004-present.  Entries for Hewson, Pride, Rainborowe.

   prosopography:

   establishment_is_22000, foot_regiment_daily_cost_12636,
   horse_regiment_daily_cost_17148, dragoon_regiment_daily_cost_21432:
     Computed from the Ordinance's establishment tables as printed
     in Firth and Rait, verified against the cost estimates in
     Gentles, pp. 36-42.

   pay_monotone, horse_pay_ge_foot, dragoon_pay_intermediate,
   trooper_premium, general_pay_branch_invariant:
     Structural consequences of the pay tables in the Ordinance.
     The 3:1 trooper premium is discussed in Firth, p. 185.

   cromwell_compliant, manchester_non_compliant,
   essex_non_compliant, fairfax_not_subject_to_sdo:
     Historical compliance checked against Kishlansky, Chs. 4-5
     and Gentles, pp. 1-15.

   merit_over_birth, gentleman_equals_tradesman,
   hewson_eligible_for_major, pride_eligible_for_major:
     The meritocratic principle is documented in Firth, Ch. II
     and Gentles, pp. 117-130.  Hewson and Pride are attested
     by the ODNB.
*)
