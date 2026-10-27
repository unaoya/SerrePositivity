module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationNullDomain
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonHomGluing

/-!
概要：元第二 Perf 値の収縮を実逆回転の元小模型へ接続する。
方針：全 Hom を持つ実像包絡に同じ収縮を読み、元 raw cone 判定を適用する。
規約：同じ対象と同じ実逆回転を保持。自然な収縮は要求しない。
使われ方：固定厚核上の V 条件の無条件化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type (u + 1)) [DGCategory R E] [Small.{u} E]
  {P : Type (u + 1)} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))

/-- 概要：元第二 Perf 値の収縮は同じ小実像内の収縮そのもの。
方針：二つの充満包含は全 Hom と単位を保持する。
規約：元収縮を選び直さない。使われ方：元 raw 比較の第二頂点。 -/
lemma dgPerfectComparisonSecond_contractible (x : P)
    (hG : ∃ t : GradedHom R (G.obj x).val (G.obj x).val (-1),
      (homObject R (RightModule R E) (G.obj x).val (G.obj x).val).d (-1) 0 t =
        (unitElement R (G.obj x).val).val) :
    ∃ t : GradedHom R ((dgPerfectComparisonSecond R E F G).obj x)
      ((dgPerfectComparisonSecond R E F G).obj x) (-1),
      (homObject R (DGPerfectComparisonBase R E F G)
        ((dgPerfectComparisonSecond R E F G).obj x)
        ((dgPerfectComparisonSecond R E F G).obj x)).d (-1) 0 t =
          (unitElement R ((dgPerfectComparisonSecond R E F G).obj x)).val := by
  exact hG

/-- 概要：元第二 Perf 値が可縮なら元実逆回転の cone は可縮。
方針：元実像包絡の同じ第二対象へ raw 逆回転判定を適用する。
規約：元二実像・元比較射を保持。使われ方：厚核制限の V 因子化条件。 -/
lemma dgPerfectComparisonInverseRotation_nullProperty
    (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G) (x : P)
    (hG : ∃ t : GradedHom R (G.obj x).val (G.obj x).val (-1),
      (homObject R (RightModule R E) (G.obj x).val (G.obj x).val).d (-1) 0 t =
        (unitElement R (G.obj x).val).val) :
    dgIdentityHomGluingNullProperty R (DGPerfectComparisonInverseRotationBase R E F G)
      ((dgPerfectComparisonInverseRotationFunctor R E F G τ).obj x) :=
  dgIdentityInverseRotation_nullProperty R (DGPerfectComparisonBase R E F G)
    (dgPerfectComparisonFirst R E F G) (dgPerfectComparisonSecond R E F G)
    (dgPerfectComparisonMap R E F G τ) (dgPerfectComparisonMap_hom_naturality R E F G τ)
    x (dgPerfectComparisonSecond_contractible R E F G x hG)

end SerrePositivity.KST.SConstruction
