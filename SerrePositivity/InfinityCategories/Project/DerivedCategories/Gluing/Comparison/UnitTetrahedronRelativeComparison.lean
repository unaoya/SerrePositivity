module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.UnitTetrahedronLoopClass
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeDiagramHomotopy
/-! # 単位四面体の同じ内角上での実相対比較

概要：二つの終側面の一致と前側面の単位退化から、退化四面体への内角固定比較を構成する。
方針：三面を curry して内角一致を示し、F1B の公開相対比較を全入力へ適用する。
規約：元四面体と三指定面を保持し、存在を追加仮定にしない。
使われ方：D の単位則から左単位閉路の零性を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K Z : SSet.{u}} (T : (Δ[3] : SSet.{u}) ⊗ K ⟶ Z)
  (U : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
  (h0 : (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ T = U)
  (h1 : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ T = U)
  (h3 : (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ T =
    (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ U)

include h0 h1 h3 in
lemma dgGluingUnitTetrahedronFamily_horn_eq :
    ((horn 3 2).ι ▷ K) ≫ T =
      ((horn 3 2).ι ▷ K) ≫ (stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTetrahedron_horn_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry U)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry_face, h0])
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry_face, h1])
    (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry_face, h3]
      apply uncurry_injective
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry, uncurry_natural_left, uncurry_curry]
      rfl)
  apply (cancel_epi (β_ K (horn 3 2 : SSet.{u})).hom).mp
  have he := congrArg uncurry hh
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexFamilyCurry, uncurry_natural_left, uncurry_curry,
    BraidedCategory.braiding_naturality_right_assoc] using he

include h0 h1 h3 in
lemma dgGluingUnitTetrahedronFamily_relative_exists [Quasicategory Z] :
    ∃ H : SSet.Homotopy T ((stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U),
      (((horn 3 2).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst ((horn 3 2 : SSet.{u}) ⊗ K) Δ[1] ≫ ((horn 3 2).ι ▷ K) ≫
          (stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U := by
  have hh := dgGluingUnitTetrahedronFamily_horn_eq T U h0 h1 h3
  have hi : innerAnodyneExtensions ((horn 3 2).ι ▷ K) :=
    (innerAnodyneExtensions.horn_ι (by decide : (0 : Fin 4) < 2)
      (by decide : (2 : Fin 4) < Fin.last 3)).whiskerRight K
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_homotopy_relative_innerAnodyne ((horn 3 2).ι ▷ K) hi
    T ((stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U) hh.symm
  refine ⟨H, ?_⟩
  exact hH.trans (congrArg (fun f => fst ((horn 3 2 : SSet.{u}) ⊗ K) Δ[1] ≫ f) hh)
include h0 h1 h3 in
lemma dgGluingUnitTetrahedronLoop_homMk_id_of_unit_face [Quasicategory Z]
    {x y : Z _⦋0⦌} (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (hB : (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  obtain ⟨H, hH⟩ := dgGluingUnitTetrahedronFamily_relative_exists T U h0 h1 h3
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTetrahedronLoop_homMk_id b l T U H hH hB ha
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
