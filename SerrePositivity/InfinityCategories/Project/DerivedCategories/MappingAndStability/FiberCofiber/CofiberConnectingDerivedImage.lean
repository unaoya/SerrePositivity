module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.SemifreeCofiberConnecting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableHomotopyChainMap

/-! # 実際の標準 cofiber 接続射の D3 による像

概要：安定構造の標準 cofiber 接続射を導来比較で写すと、cone の負の第一射影になる。
方針：接続射の端点を正規化し、鎖写像上の D3 の自然性と cone 写像の式を使う。
規約：通常の導来圏からの逆像で接続射を定義しない。使われ方：D7 の三角形の第三射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 実際の suspension への接続射を標準 cone の定値頂点間の射に正規化する。 -/
def normalizedSemifreeCofiberConnectingToSuspension (f : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)) :
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex11 f).symm) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionSquare f) ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X))

/-- 正規化した実際の接続射は標準 cone 写像の類。 -/
lemma normalizedSemifreeCofiberConnectingToSuspension_eq (f : X.val ⟶ Y.val) :
    normalizedSemifreeCofiberConnectingToSuspension f =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f))
          (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)) := by
  unfold normalizedSemifreeCofiberConnectingToSuspension
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberConnectingToSuspension]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 実際の接続射の D3 像は標準 cone の接続射と両端比較の下で一致する。 -/
lemma derivedSemifreeCofiberConnecting (f : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (normalizedSemifreeCofiberConnectingToSuspension f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
      DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0))).mor₃ := by
  rw [normalizedSemifreeCofiberConnectingToSuspension_eq]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso_naturality S
    (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f) (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)
  have hq : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom =
      (CochainComplex.mappingCone.triangle (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0))).mor₃ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap_connecting f
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom ≫
        (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f) ≫
          DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom) h
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom ≫
        DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom) :=
      congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom ≫ z)
          (DerivedCategory.Q.map_comp _ _).symm
    _ = _ := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom ≫ DerivedCategory.Q.map z) hq

/-- Q の一回シフト比較まで含む、標準 cone 三角形の第三射との一致。 -/
lemma derivedSemifreeCofiberConnecting_shift (f : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (normalizedSemifreeCofiberConnectingToSuspension f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom ≫
      DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0))).mor₃ ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom)
      (derivedSemifreeCofiberConnecting f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
