module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDG
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-!
概要：全次数 Hom end の dg 関手族を、元対象と同時に評価する tensor dg 関手。
方針：元関手の Hom 作用と end 評価を合成し、既存の符号付き中間交換律を使う。
規約：標的の Small 仮定なし。全次数の非可逆パラメータも保持する。
使われ方：元 cone end 二単体を全 native 関手族として評価する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E]
local instance : DGCategory R (DGTensorCategory R D (DGFunctor R D E)) :=
  dgTensorEnrichment R D (DGFunctor R D E)

/-- 概要：同時評価の Hom 作用は元関手作用と同じ対象での end 評価の合成。
方針：同じ豊穣合成を用いる。規約：両パラメータを保持。
使われ方：実 tensor 評価。 -/
def dgFunctorTensorEvalHom (x y : DGTensorCategory R D (DGFunctor R D E)) :
    (x ⟶[Complex R] y) ⟶ homObject R E (x.2.obj x.1) (y.2.obj y.1) :=
  (x.2.map x.1 y.1 ⊗ₘ dgFunctorHomπ R D E x.2 y.2 y.1) ≫ eComp (Complex R) _ _ _

/-- 概要：同時評価は元の二斉次成分を同じ順で評価する。
方針：tensor 純斉次元で評価。規約：全整数次数を保持。
使われ方：符号付き合成保存。 -/
lemma dgFunctorTensorEvalHom_element {x y : DGTensorCategory R D (DGFunctor R D E)}
    {p q n : ℤ} (a : GradedHom R x.1 y.1 p) (b : GradedHom R x.2 y.2 q)
    (hn : p + q = n) :
    (dgFunctorTensorEvalHom R D E x y).f n (dgTensorElement R a b hn) =
      forward R ((x.2.map x.1 y.1).f p a)
        ((dgFunctorHomπ R D E x.2 y.2 y.1).f q b) hn := by
  change (eComp (Complex R) _ _ _).f n
    ((x.2.map x.1 y.1 ⊗ₘ dgFunctorHomπ R D E x.2 y.2 y.1).f n
      (ιTensorObj (homObject R D x.1 y.1) (dgFunctorHom R D E x.2 y.2)
        p q n hn (a ⊗ₜ[R] b))) = _
  rw [tensorMap_apply]
  rfl

/-- 概要：同時評価の四重合成は交差する二次数の Koszul 符号を持つ。
方針：既存の end 自然性と中間交換律を使う。
規約：元 Hom 成分を変更しない。使われ方：tensor 評価の合成則。 -/
lemma dgFunctorTensorEvalHom_interchange
    {x y z : DGTensorCategory R D (DGFunctor R D E)} {p q r s n : ℤ}
    (a : GradedHom R x.1 y.1 p) (b : GradedHom R x.2 y.2 q)
    (c : GradedHom R y.1 z.1 r) (e : GradedHom R y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    forward R
      ((dgFunctorTensorEvalHom R D E x y).f (p + q) (dgTensorElement R a b rfl))
      ((dgFunctorTensorEvalHom R D E y z).f (r + s) (dgTensorElement R c e rfl)) hn =
    (q * r).negOnePow • (dgFunctorTensorEvalHom R D E x z).f n
      (dgTensorElement R (forward R a c rfl) (forward R b e rfl) (by omega)) := by
  simp only [dgFunctorTensorEvalHom_element, DGFunctor.map_forward, dgFunctorHomπ_forward]
  exact dgMiddleInterchange _ _ _ _ _ _ _
    (dgFunctorHomElement_naturality R D E b c rfl).symm hn

/-- 概要：元対象と全 dg 関手族を同時に評価する厳密 dg 関手。
方針：元 end の単位と符号付き交換律で tensor 圏の法則を検証する。
規約：標的に Small を要求しない。使われ方：元 native 全二単体の評価。 -/
def dgFunctorTensorEvaluation :
    DGFunctor R (DGTensorCategory R D (DGFunctor R D E)) E where
  obj x := x.2.obj x.1
  map := dgFunctorTensorEvalHom R D E
  map_id x := by
    rw [dgTensor_identity, dgFunctorTensorEvalHom, Category.assoc,
      tensorHom_comp_tensorHom_assoc, x.2.map_id]
    change (λ_ (𝟙_ (Complex R))).inv ≫
      (eId (Complex R) (x.2.obj x.1) ⊗ₘ
        (dgFunctorIdentity R D E x.2 ≫ dgFunctorHomπ R D E x.2 x.2 x.1)) ≫
          eComp (Complex R) _ _ _ = _
    rw [dgFunctorIdentity_π]
    exact dgEnrichedUnitsMultiply (x.2.obj x.1)
  map_comp x y z := by
    apply dgTensorComposition_of_elements x y z (x.2.obj x.1) (y.2.obj y.1) (z.2.obj z.1)
    intro p q r s n hn a b c e
    rw [dgTensor_forward]
    simp only [Units.smul_def, map_zsmul]
    exact (dgFunctorTensorEvalHom_interchange R D E a b c e hn).symm

/-- 概要：入力関手を固定した同時評価は元 dg 関手そのもの。
方針：元単位挿入と end 評価の単位保存を全斉次元で照合する。
規約：全 Hom の厳密等号。使われ方：native 全族の元頂点の回収。 -/
lemma dgFunctorTensorEvaluation_fixed (F : DGFunctor R D E) :
    (dgTensorIncludeFirst R D (DGFunctor R D E) F).comp
      (dgFunctorTensorEvaluation R D E) = F := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  apply (Category.comp_id _).trans
  change dgTensorFirstHom R D (DGFunctor R D E) F x y ≫
    dgFunctorTensorEvalHom R D E (x, F) (y, F) = F.map x y
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (dgFunctorTensorEvalHom R D E (x, F) (y, F)).f p
    ((dgTensorFirstHom R D (DGFunctor R D E) F x y).f p a) = (F.map x y).f p a
  rw [dgTensorFirstHom_apply]
  have hv := dgFunctorTensorEvalHom_element R D E
    (x := ((x, F) : DGTensorCategory R D (DGFunctor R D E)))
    (y := ((y, F) : DGTensorCategory R D (DGFunctor R D E)))
    a (unitElement R F).val (add_zero p)
  apply hv.trans
  have hu := DGFunctor.map_unitElement R (dgFunctorEvaluationDG R D E y) F
  change (dgFunctorHomπ R D E F F y).f 0 (unitElement R F).val =
    (unitElement R (F.obj y)).val at hu
  rw [hu]
  simpa only [compose, mul_zero, Int.negOnePow_zero, one_smul] using
    unit_compose R ((F.map x y).f p a)

end SerrePositivity.KST.SConstruction
