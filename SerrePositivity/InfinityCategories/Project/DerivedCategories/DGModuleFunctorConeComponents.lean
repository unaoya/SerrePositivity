module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorConeIso

/-! # dg 関手の cone 比較と実包含・零角

概要：cone の実同型は次数 −1 の左包含を保ち、零加群の像は閉零圏で零となる。
方針：全評価を複体値 dg 関手の同じ比較射へ帰着し、零角は恒等射の消滅で判定する。
規約：実二単体のホモトピー成分を厳密に保持。使われ方：四角形の関手同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {M N : ModuleCategory A D}

/-- cone 比較射は標準の次数 −1 左包含を元の左包含の像へ送る。 -/
lemma dgModuleFunctorConeComparison_inl (f : M ⟶ N) :
    compose A
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison A D E F f))).val
      (moduleConeInlElement A E (F.onClosed.map f)) (add_zero (-1)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeInl A D E F f := by
  apply moduleHomElement_ext A E
  intro x
  rw [moduleHomCompose_π, moduleConeInlElement_π, ← moduleEvaluation_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison_eval]
  exact DGFunctor.moduleConeImageComparison_inl A D (F.comp (moduleEvaluationDG A E x)) f

/-- 任意の dg 加群値 dg 関手の零加群像は閉零加群圏で零対象。 -/
lemma dgModuleFunctor_zero_isZero : Limits.IsZero (F.onClosed.obj (moduleZero A D)) := by
  apply (Limits.IsZero.iff_id_eq_zero _).2
  rw [← F.onClosed.map_id]
  have h := (moduleZero_isZero A D).eq_of_src (𝟙 (moduleZero A D)) 0
  rw [h, Functor.map_zero]

/-- 零角を実加群同型で標準零加群と比較する。 -/
def dgModuleFunctorZeroIso : moduleZero A E ≅ F.onClosed.obj (moduleZero A D) :=
  (moduleZero_isZero A E).iso (dgModuleFunctor_zero_isZero A D E F)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
