module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# prism の完全化：完全化から古典的 p 進完備化へ（BS 著者版 Lemma 3.9 の別系統）

## 概要
任意の δ 環の完全化の古典的 p 進完備化とその普遍性・関手性・冪等性・正則性、生成元像の d 進完備性を仮定した prism への普遍性。

## 方針
BS 著者版 Lemma 2.28・Lemma 2.34 を完全化に当てる。

## 規約
d 進完備性の仮定を外す部分は未。

## 使われ方
d で割る完全 prism の構成（Semiperfectoid/PerfectPrismDivision）、André。
-/

universe u v w

/-! ## p進完備なδ完全化と普遍性

任意のδ環のFrobenius余極限を古典的p進完備化する。
完全かつ古典的p進完備なδ環への一意な延長を具体的に証明する。
prismやperfectoid環の定義を変更せず、導来完備化との比較は別工程に残す。
-/

@[expose] public noncomputable section PCompletedDeltaPerfection

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ完全化の古典的p進完備化。 -/
abbrev PCompletedDeltaPerfection (D : DeltaStructure p A) :=
  AdicCompletion (Ideal.span {(p : DeltaPerfection D)}) (DeltaPerfection D)

/-- p進完備なδ完全化のδ構造。 -/
def pCompletedDeltaPerfectionStructure (D : DeltaStructure p A) :
    DeltaStructure p (PCompletedDeltaPerfection D) :=
  (deltaPerfectionStructure D).adicCompletion (Ideal.span {(p : DeltaPerfection D)})
    (Ideal.subset_span (by simp))

/-- 元のδ環からp進完備なδ完全化への標準射。 -/
def pCompletedDeltaPerfectionMap (D : DeltaStructure p A) : A →+* PCompletedDeltaPerfection D :=
  (algebraMap (DeltaPerfection D) _).comp (deltaPerfectionOf D 0)

/-- p進完備なδ完全化への標準射はδ射。 -/
theorem pCompletedDeltaPerfectionMap_isDeltaHom (D : DeltaStructure p A) :
    D.IsDeltaHom (pCompletedDeltaPerfectionStructure D) (pCompletedDeltaPerfectionMap D) :=
  ((deltaPerfectionStructure D).isDeltaHom_adicCompletion _
    (Ideal.subset_span (by simp))).comp (deltaPerfectionOf_isDeltaHom D 0)

/-- p進完備化後もδ完全化は完全。 -/
theorem pCompletedDeltaPerfection_isPerfect (D : DeltaStructure p A) :
    (pCompletedDeltaPerfectionStructure D).IsPerfect :=
  (deltaPerfection_isPerfect D).adicCompletion_span_p

/-- p進完備なδ完全化は、環自身のp生成イデアルに関して古典的完備。 -/
theorem pCompletedDeltaPerfection_isAdicComplete (D : DeltaStructure p A) :
    IsAdicComplete (Ideal.span {(p : PCompletedDeltaPerfection D)})
      (PCompletedDeltaPerfection D) := by
  let I : Ideal (DeltaPerfection D) := Ideal.span {(p : DeltaPerfection D)}
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  have h := AdicCompletion.isAdicComplete (M := DeltaPerfection D) hI
  have hmap : I.map (algebraMap (DeltaPerfection D) (PCompletedDeltaPerfection D)) =
      Ideal.span {(p : PCompletedDeltaPerfection D)} := by simp [I, Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff (I := I)
    (S := PCompletedDeltaPerfection D) (M := PCompletedDeltaPerfection D)).mpr h

/-- 完全かつ古典的p進完備なδ環への基底δ射は、p進完備なδ完全化から
一意なδ射へ延長する。源のp正則性・分離性・完備性は不要。 -/
theorem existsUnique_pCompletedDeltaPerfectionHom {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (E : DeltaStructure p B) (hE : E.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : B)}) B] (f : A →+* B) (hf : D.IsDeltaHom E f) :
    ∃! g : PCompletedDeltaPerfection D →+* B,
      (pCompletedDeltaPerfectionStructure D).IsDeltaHom E g ∧
        g.comp (pCompletedDeltaPerfectionMap D) = f := by
  let I : Ideal (DeltaPerfection D) := Ideal.span {(p : DeltaPerfection D)}
  let C := AdicCompletion I (DeltaPerfection D)
  let j := algebraMap (DeltaPerfection D) C
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  have hp : (p : DeltaPerfection D) ∈ I := Ideal.subset_span (by simp)
  have hj := (deltaPerfectionStructure D).isDeltaHom_adicCompletion I hp
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaPerfectionHom D E hE f hf
  have hIJ : I.map k ≤ Ideal.span {(p : B)} := by simp [I, Ideal.map_span]
  obtain ⟨g, hg, hgu⟩ := (deltaPerfectionStructure D).existsUnique_adicCompletion_lift
    E I hp hI (Ideal.span {(p : B)}) k hk.1 hIJ
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · change g.comp (j.comp (deltaPerfectionOf D 0)) = f
    rw [← RingHom.comp_assoc, hg.1, hk.2]
  · intro l hl
    have hlk : l.comp j = k := by
      apply hku (l.comp j)
      refine ⟨hl.1.comp hj, ?_⟩
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hlk, hl.1⟩

end SerrePositivity.BhattScholze

end PCompletedDeltaPerfection

/-! ## p進完備なδ完全化の正則性とdistinguished商

具体的な完全化環と標準射に、既存BS 著者版 Lemma 2.28・2.34の結果を適用する。
prismのイデアルの単項化や導来完備化との比較は結論しない。
-/

@[expose] public noncomputable section PCompletedDeltaRegularity

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p進完備なδ完全化ではp倍が単射。 -/
theorem pCompletedDeltaPerfection_p_mul_injective (D : DeltaStructure p A) :
    Function.Injective (fun x : PCompletedDeltaPerfection D ↦
      (p : PCompletedDeltaPerfection D) * x) :=
  (pCompletedDeltaPerfection_isPerfect D).p_mul_injective

/-- 基底のdistinguished元の像はdistinguished。 -/
theorem pCompletedDeltaPerfectionMap_isDistinguished (D : DeltaStructure p A)
    {d : A} (hd : D.IsDistinguished d) :
    (pCompletedDeltaPerfectionStructure D).IsDistinguished (pCompletedDeltaPerfectionMap D d) :=
  (pCompletedDeltaPerfectionMap_isDeltaHom D).map_isDistinguished hd

/-- 基底のdistinguished元の像はp進完備なδ完全化で非零因子。 -/
theorem pCompletedDeltaPerfectionMap_mul_injective (D : DeltaStructure p A)
    {d : A} (hd : D.IsDistinguished d) :
    Function.Injective (fun x : PCompletedDeltaPerfection D ↦
      pCompletedDeltaPerfectionMap D d * x) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact (pCompletedDeltaPerfection_isPerfect D).distinguished_mul_injective
    (pCompletedDeltaPerfectionMap_isDistinguished D hd)

/-- distinguished元の標準像による商では、全てのp冪ねじれがpで消える。 -/
theorem pCompletedDeltaPerfection_quotient_p_pow_torsion_killed_by_p
    (D : DeltaStructure p A) {d : A} (hd : D.IsDistinguished d)
    (N : ℕ) (x : PCompletedDeltaPerfection D ⧸ Ideal.span {pCompletedDeltaPerfectionMap D d})
    (hx : (p : PCompletedDeltaPerfection D ⧸
      Ideal.span {pCompletedDeltaPerfectionMap D d}) ^ N * x = 0) :
    (p : PCompletedDeltaPerfection D ⧸ Ideal.span {pCompletedDeltaPerfectionMap D d}) * x = 0 :=
  (pCompletedDeltaPerfection_isPerfect D).distinguished_quotient_p_pow_torsion_killed_by_p
    (pCompletedDeltaPerfectionMap_isDistinguished D hd) N x hx

end SerrePositivity.BhattScholze

end PCompletedDeltaRegularity

/-! ## p進完備なδ完全化の具体的な延長射と関手性

BS 著者版 Lemma 3.9のp進完備化段階。
既存の存在・一意性から公開環射を取り出し、恒等射・合成との両立を証明する。
(p,d)導来完備化やprismの完全化全体とは区別する。
-/

@[expose] public noncomputable section PCompletedDeltaFunctor

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

/-- 完全かつp進完備なδ終域への具体的な一意延長射。 -/
def pCompletedDeltaLift (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) : PCompletedDeltaPerfection D →+* B :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose

/-- 選んだ延長射はδ射。 -/
theorem pCompletedDeltaLift_isDeltaHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaPerfectionStructure D).IsDeltaHom E (pCompletedDeltaLift D E hE f hf) :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose_spec.1.1

/-- 延長射は元の基底射に一致する。 -/
@[simp] theorem pCompletedDeltaLift_comp_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaLift D E hE f hf).comp (pCompletedDeltaPerfectionMap D) = f :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose_spec.1.2

/-- 基底射に一致する任意のδ射は具体的な延長射と等しい。 -/
theorem pCompletedDeltaLift_unique (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) (g : PCompletedDeltaPerfection D →+* B)
    (hg : (pCompletedDeltaPerfectionStructure D).IsDeltaHom E g)
    (hgf : g.comp (pCompletedDeltaPerfectionMap D) = f) :
    g = pCompletedDeltaLift D E hE f hf :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose_spec.2 g ⟨hg, hgf⟩

/-- p進完備なδ完全化からのδ射は基底上の値で決まる。 -/
theorem pCompletedDeltaHom_ext (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f g : PCompletedDeltaPerfection D →+* B)
    (hf : (pCompletedDeltaPerfectionStructure D).IsDeltaHom E f)
    (hg : (pCompletedDeltaPerfectionStructure D).IsDeltaHom E g)
    (hfg : f.comp (pCompletedDeltaPerfectionMap D) =
      g.comp (pCompletedDeltaPerfectionMap D)) : f = g := by
  let j := pCompletedDeltaPerfectionMap D
  have hgj := hg.comp (pCompletedDeltaPerfectionMap_isDeltaHom D)
  exact (pCompletedDeltaLift_unique D E hE (g.comp j) hgj f hf hfg).trans
    (pCompletedDeltaLift_unique D E hE (g.comp j) hgj g hg rfl).symm

/-- δ射が誘導するp進完備なδ完全化の間の具体的な射。 -/
def pCompletedDeltaMap (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    PCompletedDeltaPerfection D →+* PCompletedDeltaPerfection E := by
  let := pCompletedDeltaPerfection_isAdicComplete E
  exact pCompletedDeltaLift D (pCompletedDeltaPerfectionStructure E)
    (pCompletedDeltaPerfection_isPerfect E) ((pCompletedDeltaPerfectionMap E).comp f)
    ((pCompletedDeltaPerfectionMap_isDeltaHom E).comp hf)

/-- 誘導射はδ射。 -/
theorem pCompletedDeltaMap_isDeltaHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaPerfectionStructure D).IsDeltaHom (pCompletedDeltaPerfectionStructure E)
      (pCompletedDeltaMap D E f hf) := by
  let := pCompletedDeltaPerfection_isAdicComplete E
  exact pCompletedDeltaLift_isDeltaHom D (pCompletedDeltaPerfectionStructure E)
    (pCompletedDeltaPerfection_isPerfect E) _
    ((pCompletedDeltaPerfectionMap_isDeltaHom E).comp hf)

/-- 誘導射は標準射と可換。 -/
@[simp] theorem pCompletedDeltaMap_comp_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaMap D E f hf).comp (pCompletedDeltaPerfectionMap D) =
      (pCompletedDeltaPerfectionMap E).comp f := by
  let := pCompletedDeltaPerfection_isAdicComplete E
  exact pCompletedDeltaLift_comp_map D (pCompletedDeltaPerfectionStructure E)
    (pCompletedDeltaPerfection_isPerfect E) _
    ((pCompletedDeltaPerfectionMap_isDeltaHom E).comp hf)

/-- 恒等δ射の誘導射は恒等射。 -/
@[simp] theorem pCompletedDeltaMap_id (D : DeltaStructure p A) :
    pCompletedDeltaMap D D (RingHom.id A) D.isDeltaHom_id =
      RingHom.id (PCompletedDeltaPerfection D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  apply pCompletedDeltaHom_ext D _ (pCompletedDeltaPerfection_isPerfect D)
    _ _ (pCompletedDeltaMap_isDeltaHom D D _ _) (pCompletedDeltaPerfectionStructure D).isDeltaHom_id
  simp only [pCompletedDeltaMap_comp_map, RingHom.comp_id, RingHom.id_comp]

/-- 合成δ射の誘導射は誘導射の合成。 -/
theorem pCompletedDeltaMap_comp (D : DeltaStructure p A) (E : DeltaStructure p B)
    (F : DeltaStructure p C) (f : A →+* B) (hf : D.IsDeltaHom E f)
    (g : B →+* C) (hg : E.IsDeltaHom F g) :
    pCompletedDeltaMap D F (g.comp f) (hg.comp hf) =
      (pCompletedDeltaMap E F g hg).comp (pCompletedDeltaMap D E f hf) := by
  let := pCompletedDeltaPerfection_isAdicComplete F
  apply pCompletedDeltaHom_ext D _ (pCompletedDeltaPerfection_isPerfect F)
    _ _ (pCompletedDeltaMap_isDeltaHom D F _ _)
    ((pCompletedDeltaMap_isDeltaHom E F g hg).comp (pCompletedDeltaMap_isDeltaHom D E f hf))
  rw [pCompletedDeltaMap_comp_map]
  symm
  calc
    ((pCompletedDeltaMap E F g hg).comp (pCompletedDeltaMap D E f hf)).comp
        (pCompletedDeltaPerfectionMap D) =
        (pCompletedDeltaMap E F g hg).comp
          ((pCompletedDeltaMap D E f hf).comp (pCompletedDeltaPerfectionMap D)) :=
      RingHom.comp_assoc _ _ _
    _ = (pCompletedDeltaMap E F g hg).comp ((pCompletedDeltaPerfectionMap E).comp f) := by
      rw [pCompletedDeltaMap_comp_map]
    _ = ((pCompletedDeltaMap E F g hg).comp (pCompletedDeltaPerfectionMap E)).comp f :=
      (RingHom.comp_assoc _ _ _).symm
    _ = ((pCompletedDeltaPerfectionMap F).comp g).comp f := by
      rw [pCompletedDeltaMap_comp_map]
    _ = (pCompletedDeltaPerfectionMap F).comp (g.comp f) := RingHom.comp_assoc _ _ _

end SerrePositivity.BhattScholze

end PCompletedDeltaFunctor

/-! ## 完全p進完備δ環のp進完備δ完全化からの復元

BS 著者版 Lemma 3.9のp進完備化段階の冪等性。
既に完全かつ古典的p進完備なδ環の標準射は同型で、逆射もδ射。
一般Witt復元、prismの完全化、perfectoid化の存在とは別の具体的な定理。
-/

@[expose] public noncomputable section PCompletedDeltaRecovery

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section Recovery
variable (D : DeltaStructure p A) (hD : D.IsPerfect)
variable [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- 完全p進完備δ環への、恒等基底射を延長した具体的な復元射。 -/
def pCompletedDeltaRetract : PCompletedDeltaPerfection D →+* A :=
  pCompletedDeltaLift D D hD (RingHom.id A) D.isDeltaHom_id

/-- 復元射はδ射。 -/
theorem pCompletedDeltaRetract_isDeltaHom :
    (pCompletedDeltaPerfectionStructure D).IsDeltaHom D (pCompletedDeltaRetract D hD) :=
  pCompletedDeltaLift_isDeltaHom D D hD _ _

/-- 復元射と元の標準射の合成は元環の恒等射。 -/
@[simp] theorem pCompletedDeltaRetract_comp_map :
    (pCompletedDeltaRetract D hD).comp (pCompletedDeltaPerfectionMap D) = RingHom.id A :=
  pCompletedDeltaLift_comp_map D D hD _ _

/-- 標準射と復元射の逆順の合成も、完備δ完全化の恒等射。 -/
@[simp] theorem pCompletedDeltaMap_comp_retract :
    (pCompletedDeltaPerfectionMap D).comp (pCompletedDeltaRetract D hD) =
      RingHom.id (PCompletedDeltaPerfection D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  apply pCompletedDeltaHom_ext D _ (pCompletedDeltaPerfection_isPerfect D) _ _
    ((pCompletedDeltaPerfectionMap_isDeltaHom D).comp (pCompletedDeltaRetract_isDeltaHom D hD))
    (pCompletedDeltaPerfectionStructure D).isDeltaHom_id
  rw [RingHom.comp_assoc, pCompletedDeltaRetract_comp_map, RingHom.comp_id, RingHom.id_comp]

include hD in
/-- 完全p進完備δ環の標準p進完備δ完全化射は全単射。 -/
theorem pCompletedDeltaPerfectionMap_bijective :
    Function.Bijective (pCompletedDeltaPerfectionMap D) := by
  have hl : Function.LeftInverse (pCompletedDeltaRetract D hD) (pCompletedDeltaPerfectionMap D) :=
    fun x ↦ RingHom.congr_fun (pCompletedDeltaRetract_comp_map D hD) x
  have hr : Function.RightInverse (pCompletedDeltaRetract D hD) (pCompletedDeltaPerfectionMap D) :=
    fun x ↦ RingHom.congr_fun (pCompletedDeltaMap_comp_retract D hD) x
  exact ⟨hl.injective, hr.surjective⟩

/-- 完全p進完備δ環と、その具体的なp進完備δ完全化の環同型。 -/
def pCompletedDeltaPerfectionEquiv : A ≃+* PCompletedDeltaPerfection D :=
  RingEquiv.ofBijective (pCompletedDeltaPerfectionMap D)
    (pCompletedDeltaPerfectionMap_bijective D hD)

/-- 復元同型の順射は標準射。 -/
@[simp] theorem pCompletedDeltaPerfectionEquiv_toRingHom :
    (pCompletedDeltaPerfectionEquiv D hD).toRingHom = pCompletedDeltaPerfectionMap D := rfl

/-- 復元同型の逆射は恒等基底射の一意延長として選んだ復元射。 -/
@[simp] theorem pCompletedDeltaPerfectionEquiv_symm_toRingHom :
    (pCompletedDeltaPerfectionEquiv D hD).symm.toRingHom = pCompletedDeltaRetract D hD := by
  apply RingHom.ext
  intro x
  apply (pCompletedDeltaPerfectionMap_bijective D hD).1
  change (pCompletedDeltaPerfectionEquiv D hD)
    ((pCompletedDeltaPerfectionEquiv D hD).symm x) =
      pCompletedDeltaPerfectionMap D (pCompletedDeltaRetract D hD x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (pCompletedDeltaMap_comp_retract D hD) x).symm

/-- 復元同型は具体的な主イデアルによる商にも標準写像と両立する同型を誘導する。 -/
def pCompletedDeltaPerfectionQuotientEquiv (d : A) :
    A ⧸ Ideal.span {d} ≃+*
      PCompletedDeltaPerfection D ⧸ Ideal.span {pCompletedDeltaPerfectionMap D d} :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaPerfectionEquiv D hD)
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

/-- 誘導商同型は、代表元に標準p進完備δ完全化射を適用する。 -/
@[simp] theorem pCompletedDeltaPerfectionQuotientEquiv_mk (d x : A) :
    pCompletedDeltaPerfectionQuotientEquiv D hD d (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {pCompletedDeltaPerfectionMap D d})
        (pCompletedDeltaPerfectionMap D x) := rfl

end Recovery

/-- 任意のδ環のp進完備δ完全化をもう一度同じ操作で完全化しても同型。
任意の源のp正則性・古典的完備性は要求しない。 -/
def pCompletedDeltaPerfectionIdempotentEquiv (D : DeltaStructure p A) :
    PCompletedDeltaPerfection D ≃+*
      PCompletedDeltaPerfection (pCompletedDeltaPerfectionStructure D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact pCompletedDeltaPerfectionEquiv _ (pCompletedDeltaPerfection_isPerfect D)

/-- 冪等同型の順射は二段目の標準射。 -/
@[simp] theorem pCompletedDeltaPerfectionIdempotentEquiv_toRingHom (D : DeltaStructure p A) :
    (pCompletedDeltaPerfectionIdempotentEquiv D).toRingHom =
      pCompletedDeltaPerfectionMap (pCompletedDeltaPerfectionStructure D) := rfl

/-- 具体的なp進完備δ完全化は実導来p完備でもある。
共通の古典的完備→導来完備比較を適用し、導来完備化対象との同定は結論しない。 -/
theorem pCompletedDeltaPerfection_isModuleComplete (D : DeltaStructure p A) :
    DerivedCompletion.IsModuleComplete (PCompletedDeltaPerfection D)
      (p : PCompletedDeltaPerfection D)
      (ModuleCat.of (PCompletedDeltaPerfection D) (PCompletedDeltaPerfection D)) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact DerivedCompletion.isModuleComplete_of_isAdicComplete (PCompletedDeltaPerfection D)
    (p : PCompletedDeltaPerfection D) _

end SerrePositivity.BhattScholze

end PCompletedDeltaRecovery

/-! ## d進完備性を明示したp進完備δ完全化のprismと普遍性

BS 著者版 Lemma 3.9の主イデアル・distinguished生成元の場合の部分定理。
p進完備δ完全化での生成元像のd進完備性を仮定し、実導来条件を持つ完全prismを
具体的に構成する。この完備性自体や一般Cartierイデアルの単項化は結論しない。
-/

@[expose] public noncomputable section PCompletedDistinguishedPrism

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (hd : D.IsDistinguished d)
variable [IsAdicComplete (Ideal.span {pCompletedDeltaPerfectionMap D d})
  (PCompletedDeltaPerfection D)]

/-- distinguished生成元の像がd進完備なp進完備δ完全化上の具体的なoriented prism。 -/
def pCompletedDistinguishedPrism : OrientedPrism p (PCompletedDeltaPerfection D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact OrientedPrism.ofPerfectCompleteDistinguished (pCompletedDeltaPerfectionStructure D)
    (pCompletedDeltaPerfection_isPerfect D) (pCompletedDeltaPerfectionMap D d)
    (pCompletedDeltaPerfectionMap_isDistinguished D hd)

/-- 構成したprismのδ構造は既存のp進完備δ完全化のδ構造。 -/
@[simp] theorem pCompletedDistinguishedPrism_deltaStructure :
    (pCompletedDistinguishedPrism D d hd).deltaStructure =
      pCompletedDeltaPerfectionStructure D := rfl

/-- 構成したprismの選択生成元は元のdの標準像。 -/
@[simp] theorem pCompletedDistinguishedPrism_generator :
    (pCompletedDistinguishedPrism D d hd).generator = pCompletedDeltaPerfectionMap D d := rfl

/-- 構成したprismのイデアルは元の(d)の標準射による像。 -/
theorem pCompletedDistinguishedPrism_ideal :
    (pCompletedDistinguishedPrism D d hd).ideal =
      (Ideal.span {d}).map (pCompletedDeltaPerfectionMap D) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- 具体的なprismは完全。 -/
theorem pCompletedDistinguishedPrism_isPerfect :
    (pCompletedDistinguishedPrism D d hd).deltaStructure.IsPerfect :=
  pCompletedDeltaPerfection_isPerfect D

/-- distinguished元を終域のprismイデアルへ送るδ基底射は、
構成したprismから完全oriented prismへの一意な射に延長する。 -/
theorem existsUnique_pCompletedDistinguishedPrismHom
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    ∃! g : OrientedPrism.Hom (pCompletedDistinguishedPrism D d hd) Q,
      g.toRingHom.comp (pCompletedDeltaPerfectionMap D) = f := by
  let := Q.isAdicComplete_p_of_perfect hQ
  let g := pCompletedDeltaLift D Q.deltaStructure hQ f hf
  have hgj : g.comp (pCompletedDeltaPerfectionMap D) = f := pCompletedDeltaLift_comp_map D _ _ _ _
  have hgd : (pCompletedDeltaPerfectionStructure D).IsDeltaHom Q.deltaStructure g :=
    pCompletedDeltaLift_isDeltaHom D _ _ _ _
  have hgi : (pCompletedDistinguishedPrism D d hd).ideal ≤ Q.ideal.comap g := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change g (pCompletedDeltaPerfectionMap D d) ∈ Q.ideal
    rw [show g (pCompletedDeltaPerfectionMap D d) = f d from RingHom.congr_fun hgj d]
    exact hdf
  let G : OrientedPrism.Hom (pCompletedDistinguishedPrism D d hd) Q := ⟨g, hgd, hgi⟩
  refine ⟨G, hgj, ?_⟩
  intro H hH
  apply OrientedPrism.Hom.ext
  exact pCompletedDeltaLift_unique D Q.deltaStructure hQ f hf H.toRingHom H.map_delta hH

/-- 上の一意性の具体的な公開射。 -/
def pCompletedDistinguishedPrismLift
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    OrientedPrism.Hom (pCompletedDistinguishedPrism D d hd) Q :=
  (existsUnique_pCompletedDistinguishedPrismHom D d hd Q hQ f hf hdf).choose

/-- prism延長射は標準基底射と可換する。 -/
@[simp] theorem pCompletedDistinguishedPrismLift_comp_map
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    (pCompletedDistinguishedPrismLift D d hd Q hQ f hf hdf).toRingHom.comp
      (pCompletedDeltaPerfectionMap D) = f :=
  (existsUnique_pCompletedDistinguishedPrismHom D d hd Q hQ f hf hdf).choose_spec.1

/-- 元の生成元の延長像は、終域のprismイデアルを生成する。
単なるイデアル包含ではなく、完全prism間の射の像イデアル一致を使う。 -/
theorem pCompletedDistinguishedPrismLift_map_ideal
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    (pCompletedDistinguishedPrism D d hd).ideal.map
      (pCompletedDistinguishedPrismLift D d hd Q hQ f hf hdf).toRingHom = Q.ideal :=
  (pCompletedDistinguishedPrismLift D d hd Q hQ f hf hdf).map_ideal_eq

end SerrePositivity.BhattScholze

end PCompletedDistinguishedPrism

/-! ## p進完備δ完全化のprismへの標準射と普遍性

distinguished生成元を持つoriented prismについて、生成元像のd進完備性を
明示した普遍性を証明する。既に完全なprismなら、その追加完備性も復元同型から供給する。
一般prismの完全化の存在や導来(p,d)完備化との比較は結論しない。
-/

@[expose] public noncomputable section PCompletedPrismUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section Universal
variable (P : OrientedPrism p A) (hd : P.deltaStructure.IsDistinguished P.generator)
variable [IsAdicComplete
  (Ideal.span {pCompletedDeltaPerfectionMap P.deltaStructure P.generator})
  (PCompletedDeltaPerfection P.deltaStructure)]

/-- 元のoriented prismから具体的なp進完備δ完全化prismへの標準射。 -/
def pCompletedPrismMap : OrientedPrism.Hom P
    (pCompletedDistinguishedPrism P.deltaStructure P.generator hd) := by
  refine ⟨pCompletedDeltaPerfectionMap P.deltaStructure,
    pCompletedDeltaPerfectionMap_isDeltaHom P.deltaStructure, ?_⟩
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- 完全な向き付き prism への射は、標準 prism 射を通じて一意に延長する（BS 著者版 Lemma 3.9 の普遍性で、完全化後に d 進完備性を仮定）。 -/
theorem existsUnique_pCompletedPrismHom
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom P Q) :
    ∃! g : OrientedPrism.Hom
      (pCompletedDistinguishedPrism P.deltaStructure P.generator hd) Q,
      g.comp (pCompletedPrismMap P hd) = f := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_pCompletedDistinguishedPrismHom
    P.deltaStructure P.generator hd Q hQ f.toRingHom f.map_delta f.map_generator_mem
  refine ⟨g, OrientedPrism.Hom.ext hg, ?_⟩
  intro H hH
  apply hgu H
  exact congrArg OrientedPrism.Hom.toRingHom hH

end Universal

/-- 既に完全なoriented prismでは、p進完備δ完全化上の生成元像のd進完備性も証明できる。
源の実導来条件を古典的条件へ比較し、証明済みの復元同型で運ぶ。 -/
theorem pCompletedPerfectPrism_isAdicComplete_generator
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    IsAdicComplete (Ideal.span {pCompletedDeltaPerfectionMap P.deltaStructure P.generator})
      (PCompletedDeltaPerfection P.deltaStructure) := by
  let := P.isAdicComplete_p_of_perfect hP
  let := P.isAdicComplete_generator
  let e := pCompletedDeltaPerfectionEquiv P.deltaStructure hP
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {P.generator}) e).mpr
    (P.isAdicComplete_generator)
  have he : (Ideal.span {P.generator}).map e.toRingHom =
      Ideal.span {pCompletedDeltaPerfectionMap P.deltaStructure P.generator} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  change IsAdicComplete ((Ideal.span {P.generator}).map e.toRingHom)
    (PCompletedDeltaPerfection P.deltaStructure) at h
  rw [he] at h
  exact h

/-- 既に完全なoriented prismのp進完備δ完全化上のprism。
生成元像の完備性を追加仮定せず、上の復元定理で内部に供給する。 -/
def pCompletedPerfectPrism (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    OrientedPrism p (PCompletedDeltaPerfection P.deltaStructure) := by
  let := pCompletedPerfectPrism_isAdicComplete_generator P hP
  exact pCompletedDistinguishedPrism P.deltaStructure P.generator (P.isDistinguished_generator)

/-- 復元対象のprismも完全。 -/
theorem pCompletedPerfectPrism_isPerfect (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : (pCompletedPerfectPrism P hP).deltaStructure.IsPerfect :=
  pCompletedDeltaPerfection_isPerfect P.deltaStructure

/-- 既に完全なprismからの具体的な標準prism射。 -/
def pCompletedPerfectPrismMap (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    OrientedPrism.Hom P (pCompletedPerfectPrism P hP) := by
  let := pCompletedPerfectPrism_isAdicComplete_generator P hP
  exact pCompletedPrismMap P (P.isDistinguished_generator)

/-- 既に完全なprismの標準射は、台環で全単射。 -/
theorem pCompletedPerfectPrismMap_bijective (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    Function.Bijective (pCompletedPerfectPrismMap P hP).toRingHom := by
  let := P.isAdicComplete_p_of_perfect hP
  exact pCompletedDeltaPerfectionMap_bijective P.deltaStructure hP

/-- 完全prismの標準射は標準商上でも全単射。 -/
theorem pCompletedPerfectPrismMap_quotientMap_bijective (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    Function.Bijective (pCompletedPerfectPrismMap P hP).quotientMap :=
  (pCompletedPerfectPrismMap P hP).quotientMap_bijective
    (pCompletedPerfectPrismMap_bijective P hP)

/-- 既に完全なprismへ戻る具体的な逆prism射。既存の同型判定から構成する。 -/
def pCompletedPerfectPrismInverse (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    OrientedPrism.Hom (pCompletedPerfectPrism P hP) P :=
  (pCompletedPerfectPrismMap P hP).inverseOfQuotient
    (pCompletedPerfectPrismMap_quotientMap_bijective P hP)

/-- 逆prism射と標準prism射の合成は、元prismの恒等射。 -/
@[simp] theorem pCompletedPerfectPrismInverse_comp_map (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    (pCompletedPerfectPrismInverse P hP).comp (pCompletedPerfectPrismMap P hP) =
      OrientedPrism.Hom.id P :=
  (pCompletedPerfectPrismMap P hP).inverseOfQuotient_comp
    (pCompletedPerfectPrismMap_quotientMap_bijective P hP)

/-- 標準prism射と逆prism射の逆順の合成も、完全化prismの恒等射。 -/
@[simp] theorem pCompletedPerfectPrismMap_comp_inverse (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) :
    (pCompletedPerfectPrismMap P hP).comp (pCompletedPerfectPrismInverse P hP) =
      OrientedPrism.Hom.id (pCompletedPerfectPrism P hP) :=
  (pCompletedPerfectPrismMap P hP).comp_inverseOfQuotient
    (pCompletedPerfectPrismMap_quotientMap_bijective P hP)

end SerrePositivity.BhattScholze

end PCompletedPrismUniversal

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.9" (partial := special) "向き付き prism の場合に原典の形の定理がある（BS-W17）：classicalPrismPerfection（δ 完全化の (p,d) 完備化 H⁰、完全・有界）と、完全 prism への射についての普遍性 existsUnique_classicalPrismPerfectionHom。源の完全性は仮定しない。部品（完全δ環＋distinguished 元の PD 完備化が完全 prism で普遍、完全化と完備化の順序比較）も本体。付随の主張は一つの定理には入っていない。p 進完備化した段での正則性などは PCompletedPerfection:124–145 に別の定理としてある。未完備の A_perf についての主張と、導来と古典的完備化の一致は本体にない。PCompleted 版は d 進完備性を仮定。A3/A5 の始完全 prism で使う ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：deltaPDCompletionPerfectionEquiv（原文の古典完備化との一致や普遍性とは別の比較同型。module docstring の関連を残す。） ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_pCompletedPrismHom
