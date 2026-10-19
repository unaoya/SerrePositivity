module
public import SerrePositivity.InfinityCategories.Derived.SuspensionObjectNaturality
public import SerrePositivity.InfinityCategories.Derived.HomotopyChainMapSurjectivity

/-! # D3 比較の suspension と導来圏シフトの自然な対象比較

概要：D3 比較の前後の一回シフトを、すべての定値頂点間の h の射に対して自然に比較する。
方針：Q の対象を D3 の対象へ戻し、すべての h の射を鎖写像で代表する。
規約：全整数の CommShift は後続。使われ方：D7 の自然同型の組み立て。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- suspension の D3 像と D3 の像の一回シフトの比較。 -/
def derivedSuspensionShiftObjectIso (X : Semifree S) :
    (derivedStableHomotopyEquivalence S).functor.obj
      ((suspensionFunctor (derivedInfinityCategory S)).obj
        (SSet.HomotopyCategory.mk (Simplex.vertex X))) ≅
      ((derivedStableHomotopyEquivalence S).functor.obj
        (SSet.HomotopyCategory.mk (Simplex.vertex X)))⟦(1 : ℤ)⟧ :=
  derivedSuspensionObjectIso S X ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (derivedStableHomotopyEquivalenceVertexIso S X).symm

/-- 一回シフト比較は鎖写像の類に対して自然。 -/
lemma derivedSuspensionShiftObjectIso_naturality_chainMap {X Y : Semifree S}
    (a : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        ((suspensionFunctor (derivedInfinityCategory S)).map
          (SSet.Truncated.HomotopyCategory.homMk
            (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a))) ≫
      (derivedSuspensionShiftObjectIso S Y).hom =
    (derivedSuspensionShiftObjectIso S X).hom ≫
      ((derivedStableHomotopyEquivalence S).functor.map
        (SSet.Truncated.HomotopyCategory.homMk
          (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a)))⟦(1 : ℤ)⟧' := by
  let F := (derivedStableHomotopyEquivalence S).functor
  let f := SSet.Truncated.HomotopyCategory.homMk
    (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a)
  let VX := derivedStableHomotopyEquivalenceVertexIso S X
  let VY := derivedStableHomotopyEquivalenceVertexIso S Y
  have hV := derivedStableHomotopyEquivalenceVertexIso_naturality S a
  change F.map f ≫ VY.hom = VX.hom ≫ DerivedCategory.Q.map a at hV
  have hInv : DerivedCategory.Q.map a ≫ VY.inv = VX.inv ≫ F.map f := by
    calc
      _ = VX.inv ≫ (VX.hom ≫ DerivedCategory.Q.map a) ≫ VY.inv := by simp
      _ = VX.inv ≫ (F.map f ≫ VY.hom) ≫ VY.inv := by rw [← hV]
      _ = _ := by simp
  have hShift := congrArg (shiftFunctor (DerivedCategory (ModuleCat S)) (1 : ℤ)).map hInv
  simp only [Functor.map_comp] at hShift
  have h := derivedSuspensionObjectIso_naturality S a
  dsimp only [derivedSuspensionShiftObjectIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  calc
    _ = (derivedSuspensionObjectIso S X).hom ≫
        ((DerivedCategory.Q.map a)⟦(1 : ℤ)⟧' ≫ VY.inv⟦(1 : ℤ)⟧') := by
      simpa only [Category.assoc, F, f, VY] using congrArg
        (fun z => z ≫ VY.inv⟦(1 : ℤ)⟧') h
    _ = (derivedSuspensionObjectIso S X).hom ≫
        (VX.inv⟦(1 : ℤ)⟧' ≫ (F.map f)⟦(1 : ℤ)⟧') := by rw [hShift]
    _ = _ := by simp only [Category.assoc, F, f, VX]

/-- 一回シフト比較は、定値頂点間のすべての h D(S) の射に対して自然。 -/
lemma derivedSuspensionShiftObjectIso_naturality {X Y : Semifree S}
    (f : (SSet.HomotopyCategory.mk (Simplex.vertex X) :
      derivedStableHomotopyCategory S) ⟶ SSet.HomotopyCategory.mk (Simplex.vertex Y)) :
    (derivedStableHomotopyEquivalence S).functor.map
        ((suspensionFunctor (derivedInfinityCategory S)).map f) ≫
      (derivedSuspensionShiftObjectIso S Y).hom =
    (derivedSuspensionShiftObjectIso S X).hom ≫
      ((derivedStableHomotopyEquivalence S).functor.map f)⟦(1 : ℤ)⟧' := by
  obtain ⟨a, rfl⟩ := derivedHomotopyHom_chainMap_surjective f
  exact derivedSuspensionShiftObjectIso_naturality_chainMap S a

end SerrePositivity.InfinityCategories
