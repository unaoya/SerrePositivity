module
public import SerrePositivity.InfinityCategories.Derived.CofiberTriangleImageMorphism
public import SerrePositivity.InfinityCategories.Derived.CofiberConnectingSourceTransport
public import SerrePositivity.InfinityCategories.Derived.SuspensionShiftVertexTransport
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberVertexComparison

/-! # 標準 cofiber 三角形の像の第三可換式

概要：D3 の mapTriangle が与える第三射は、標準 cone 三角形の接続射と両端比較の下で一致する。
方針：一回シフトの比較を suspension に戻し、始点・終点の輸送と実接続射の像を合成する。
規約：実際の CommShift の第三射を使う。使われ方：D7 の三角形全体の像の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : Semifree S}

/-- D3 で写した標準 cofiber 三角形の第三射は古典的 cone 接続射と可換。 -/
lemma derivedStandardCofiberTriangle_comm₃ (f : X.val ⟶ Y.val) :
    ((derivedStableHomotopyEquivalence S).functor.mapTriangle.obj
        (cofiberTriangle (semifreeCofiberZeroTriangle f)
          (semifreeCofiberZeroTriangle_isCofiberSequence f))).mor₃ ≫
      (derivedStandardCofiberSourceIso f).hom⟦(1 : ℤ)⟧' =
    (derivedStandardCofiberTargetIso f).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (cofiberDifference f (0 : X.val ⟶ 0))).mor₃ ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  let F := (derivedStableHomotopyEquivalence S).functor
  let t := semifreeCofiberZeroTriangle f
  let ht := semifreeCofiberZeroTriangle_isCofiberSequence f
  let e0 := eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex00 f))
  let e3 := eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex11 f))
  let es := eqToHom (congrArg SSet.HomotopyCategory.mk (semifreeSuspensionSquare_vertex X))
  let g := cofiberConnectingToSuspension t ht (semifreeCofiberSuspensionSquare f)
  let V := (derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X)).hom
  let P := DerivedCategory.Q.map (semifreeSuspensionComplexIso X).hom
  let c := ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom
  let VZ := (derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)).hom
  let R := DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
    (cofiberDifference f (0 : X.val ⟶ 0))).mor₃
  have hp := derivedSuspensionShiftIso_transport_vertex S t.hoShortComplex.X₁ X
    (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex00 f))
  have hc := semifreeCofiberConnecting_source_transport f
  have he := semifreeCofiberConnecting_target_transport f
  have hv := derivedSuspensionObjectIso_cancel_inv S X
  have hi := derivedSemifreeCofiberConnecting_shift f
  rw [derivedCofiberTriangle_mor₃]
  simp only [derivedStandardCofiberSourceIso, derivedStandardCofiberTargetIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, eqToIso.hom, CategoryTheory.Functor.map_comp, Category.assoc]
  change F.map (cofiberConnecting t ht) ≫
      (derivedSuspensionShiftIso S).hom.app t.hoShortComplex.X₁ ≫
      (F.map e0)⟦(1 : ℤ)⟧' ≫ (derivedStableHomotopyEquivalenceVertexIso S X).hom⟦(1 : ℤ)⟧' =
    F.map e3 ≫ VZ ≫ R ≫ c
  calc
    _ = F.map (cofiberConnecting t ht) ≫
        (F.map ((suspensionFunctor (derivedInfinityCategory S)).map e0) ≫
          (derivedSuspensionObjectIso S X).hom) :=
      congrArg (fun z => F.map (cofiberConnecting t ht) ≫ z) hp
    _ = F.map (cofiberConnecting t ht ≫
        (suspensionFunctor (derivedInfinityCategory S)).map e0) ≫
        (derivedSuspensionObjectIso S X).hom := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map (g ≫ (semifreeSuspensionSquare X).suspensionFunctorObjIso.inv) ≫
        (derivedSuspensionObjectIso S X).hom :=
      congrArg (fun z => F.map z ≫ (derivedSuspensionObjectIso S X).hom) hc
    _ = F.map g ≫ (F.map (semifreeSuspensionSquare X).suspensionFunctorObjIso.inv ≫
        (derivedSuspensionObjectIso S X).hom) := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map g ≫ (F.map es ≫ V ≫ P ≫ c) :=
      congrArg (fun z => F.map g ≫ z) hv
    _ = F.map (g ≫ es) ≫ V ≫ P ≫ c := by
      rw [CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
    _ = F.map (e3 ≫ normalizedSemifreeCofiberConnectingToSuspension f) ≫ V ≫ P ≫ c :=
      congrArg (fun z => F.map z ≫ V ≫ P ≫ c) he
    _ = F.map e3 ≫ (F.map (normalizedSemifreeCofiberConnectingToSuspension f) ≫ V ≫ P ≫ c) := by
      rw [CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
    _ = F.map e3 ≫ (VZ ≫ R ≫ c) := congrArg (fun z => F.map e3 ≫ z) hi
    _ = _ := rfl

end SerrePositivity.InfinityCategories
