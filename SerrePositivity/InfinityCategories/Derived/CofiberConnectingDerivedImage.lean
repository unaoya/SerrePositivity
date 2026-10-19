module
public import SerrePositivity.InfinityCategories.Derived.SemifreeCofiberConnecting
public import SerrePositivity.InfinityCategories.Derived.StableHomotopyChainMap

/-! # 実際の標準 cofiber 接続射の D3 による像

概要：安定構造の標準 cofiber 接続射を導来比較で写すと、cone の負の第一射影になる。
方針：接続射の端点を正規化し、鎖写像上の D3 の自然性と cone 写像の式を使う。
規約：通常の導来圏からの逆像で接続射を定義しない。使われ方：D7 の三角形の第三射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 実際の suspension への接続射を標準 cone の定値頂点間の射に正規化する。 -/
def normalizedSemifreeCofiberConnectingToSuspension (f : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (Simplex.vertex (semifreeCofiberZeroObject f)) :
      derivedStableHomotopyCategory S) ⟶
      SSet.HomotopyCategory.mk (Simplex.vertex (semifreeSuspensionObject X)) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex11 f).symm) ≫
    cofiberConnectingToSuspension (semifreeCofiberZeroTriangle f)
      (semifreeCofiberZeroTriangle_isCofiberSequence f) (semifreeCofiberSuspensionSquare f) ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeSuspensionSquare_vertex X))

/-- 正規化した実際の接続射は標準 cone 写像の類。 -/
lemma normalizedSemifreeCofiberConnectingToSuspension_eq (f : X.val ⟶ Y.val) :
    normalizedSemifreeCofiberConnectingToSuspension f =
      SSet.Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex (semifreeCofiberZeroObject f))
          (y := Simplex.vertex (semifreeSuspensionObject X)) (cofiberToSuspensionMap f)) := by
  unfold normalizedSemifreeCofiberConnectingToSuspension
  rw [semifreeCofiberConnectingToSuspension]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 実際の接続射の D3 像は標準 cone の接続射と両端比較の下で一致する。 -/
lemma derivedSemifreeCofiberConnecting (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        (normalizedSemifreeCofiberConnectingToSuspension f) ≫
      (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom ≫
      DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom =
    (derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (cofiberDifference f (0 : X.val ⟶ 0))).mor₃ := by
  rw [normalizedSemifreeCofiberConnectingToSuspension_eq]
  have h := derivedStableHomotopyEquivalenceVertexIso_naturality S
    (X := semifreeCofiberZeroObject f) (Y := semifreeSuspensionObject X) (cofiberToSuspensionMap f)
  have hq : cofiberToSuspensionMap f ≫ (semifreeSuspensionComplexIso X).hom =
      (CochainComplex.mappingCone.triangle (cofiberDifference f (0 : X.val ⟶ 0))).mor₃ :=
    cofiberToSuspensionMap_connecting f
  calc
    _ = (derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)).hom ≫
        (DerivedCategory.Q.map (cofiberToSuspensionMap f) ≫
          DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom) h
    _ = (derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)).hom ≫
        DerivedCategory.Q.map (cofiberToSuspensionMap f ≫ (semifreeSuspensionComplexIso X).hom) :=
      congrArg (fun z => (derivedStableHomotopyEquivalenceVertexIso S
        (semifreeCofiberZeroObject f)).hom ≫ z)
          (DerivedCategory.Q.map_comp _ _).symm
    _ = _ := congrArg (fun z => (derivedStableHomotopyEquivalenceVertexIso S
      (semifreeCofiberZeroObject f)).hom ≫ DerivedCategory.Q.map z) hq

/-- Q の一回シフト比較まで含む、標準 cone 三角形の第三射との一致。 -/
lemma derivedSemifreeCofiberConnecting_shift (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        (normalizedSemifreeCofiberConnectingToSuspension f) ≫
      (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom ≫
      DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom =
    (derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (cofiberDifference f (0 : X.val ⟶ 0))).mor₃ ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom)
      (derivedSemifreeCofiberConnecting f)

end SerrePositivity.InfinityCategories
