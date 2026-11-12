module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSeedExtensionRange
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition
/-!
概要：共通源への seed 精密化を、同じ標的での元の実評価のホモトピー同型へ運ぶ。
方針：全 seed の延長被覆と、同じ実 graph 延長の合成比較を合成する。
規約：入力関手の因子分解を保持し、標的の Hom 射の持ち上げを結論しない。
使われ方：c′ の異なる出発提示を一つの提示へまとめた後の実値の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (I : DGFunctor R C E) (L : DGFunctor R E D)
  (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

include hκ hreg in
lemma dgKappaClosedProjectiveSeed_extension_composition_homotopyRange
    (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R C κ).1) :
    ∃ M : ModuleCategory R E, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R E κ M ∧
      Nonempty ((moduleToHomotopy R D).obj ((dgModuleExtension R E D L).onClosed.obj M) ≅
        (moduleToHomotopy R D).obj ((dgModuleExtension R C D (I.comp L)).onClosed.obj
          (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R C κ).2 i).val))) := by
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveSeed_extension_homotopyRange R C E I κ hκ hreg i
  let N : ModuleCategory R C := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R C κ).2 i).val
  let ec := dgModuleExtensionCompositionAt R C E D I L
    (ForgetEnrichment.to (Complex R) N)
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (dgModuleExtension R E D L).onHomotopy.mapIso e ≪≫
    (moduleToHomotopy R D).mapIso ec

end SerrePositivity.InfinityCategories.Project.DerivedCategories
