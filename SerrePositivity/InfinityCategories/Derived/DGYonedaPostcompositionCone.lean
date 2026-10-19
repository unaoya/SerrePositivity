module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaPostcomposition
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.InfinityCategories.Derived.DGYonedaGradedPrimitives

/-! # 元の Hom 後合成の cone と Yoneda 加群 cone への Hom

概要：元の後合成鎖写像の cone を、Yoneda 加群 cone への全 Hom と実鎖同型で比較する。
方針：加群 cone の対象ごとの評価と、全 Hom の Yoneda 鎖同型を合成する。
規約：導来圏だけの同型に弱めない。使われ方：有限 cell 分母の消去を二未知残差へ適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定した元の閉射の Yoneda 像の実加群 cone。 -/
abbrev dgYonedaClosedCone {y z : ClosedCategory A D} (g : y ⟶ z) : ModuleCategory A D :=
  moduleCone A D ((dgYoneda A D).onClosed.map g)

/-- 元の後合成の cone は、Yoneda 加群 cone の評価と厳密に等しい。 -/
lemma dgYonedaPostcompositionCone_eq (x : D) {y z : ClosedCategory A D} (g : y ⟶ z) :
    mappingCone (dgCyclePostcomposition A D x (closedHomEquiv A D y z g)) =
      (moduleEvaluation A D x).obj (dgYonedaClosedCone A D g) := by
  change mappingCone (dgCyclePostcomposition A D x (closedHomEquiv A D y z g)) =
    mappingCone ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g))
  exact congrArg (fun f : homObject A D x y ⟶ homObject A D x z => mappingCone f)
    (dgYonedaEvaluation_postcomposition A D x g).symm

/-- 元の後合成 cone と、表現可能加群から Yoneda 加群 cone への全 Hom の実鎖同型。 -/
def dgYonedaPostcompositionConeIso (x : D) {y z : ClosedCategory A D} (g : y ⟶ z) :
    mappingCone (dgCyclePostcomposition A D x (closedHomEquiv A D y z g)) ≅
      moduleHom A D (representable A x)
        (ForgetEnrichment.to (Complex A) (dgYonedaClosedCone A D g)) :=
  (eqToIso (dgYonedaPostcompositionCone_eq A D x g)) ≪≫
    (dgYonedaIso A x (ForgetEnrichment.to (Complex A) (dgYonedaClosedCone A D g))).symm

/-- 実鎖同型で移した残差の原始元の存在は、元の cone の原始元の存在と同値。 -/
lemma dgYonedaPostcompositionCone_exists_primitive_iff (x : D)
    {y z : ClosedCategory A D} (g : y ⟶ z) (k n : ℤ)
    (a : (mappingCone (dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).X n) :
    (∃ h : (moduleHom A D (representable A x)
        (ForgetEnrichment.to (Complex A) (dgYonedaClosedCone A D g))).X k,
      (moduleHom A D (representable A x)
        (ForgetEnrichment.to (Complex A) (dgYonedaClosedCone A D g))).d k n h =
          (dgYonedaPostcompositionConeIso A D x g).hom.f n a) ↔
      ∃ h : (mappingCone (dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).X k,
        (mappingCone (dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).d k n h = a :=
  dgComplexIso_exists_primitive_iff A (dgYonedaPostcompositionConeIso A D x g).hom k n a

end SerrePositivity.InfinityCategories
