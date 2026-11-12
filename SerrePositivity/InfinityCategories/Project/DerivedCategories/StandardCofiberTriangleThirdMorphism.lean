module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberTriangleImageMorphism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberConnectingSourceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SuspensionShiftVertexTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardCofiberVertexComparison

/-! # 標準 cofiber 三角形の像の第三可換式

概要：D3 の mapTriangle が与える第三射は、標準 cone 三角形の接続射と両端比較の下で一致する。
方針：一回シフトの比較を suspension に戻し、始点・終点の輸送と実接続射の像を合成する。
規約：実際の CommShift の第三射を使う。使われ方：D7 の三角形全体の像の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- D3 で写した標準 cofiber 三角形の第三射は古典的 cone 接続射と可換。 -/
lemma derivedStandardCofiberTriangle_comm₃ (f : X.val ⟶ Y.val) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapTriangle.obj
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f))).mor₃ ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberSourceIso f).hom⟦(1 : ℤ)⟧' =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberTargetIso f).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : X.val ⟶ 0))).mor₃ ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom := by
  let F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f
  let ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f
  let e0 := eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex00 f))
  let e3 := eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex11 f))
  let es := eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X))
  let g := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionSquare f)
  let V := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)).hom
  let P := DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X).hom
  let c := ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom
  let VZ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)).hom
  let R := DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f (0 : X.val ⟶ 0))).mor₃
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIso_transport_vertex S t.hoShortComplex.X₁ X
    (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex00 f))
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberConnecting_source_transport f
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberConnecting_target_transport f
  have hv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso_cancel_inv S X
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSemifreeCofiberConnecting_shift f
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedCofiberTriangle_mor₃]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberSourceIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberTargetIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, eqToIso.hom, CategoryTheory.Functor.map_comp, Category.assoc]
  change F.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftIso S).hom.app t.hoShortComplex.X₁ ≫
      (F.map e0)⟦(1 : ℤ)⟧' ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X).hom⟦(1 : ℤ)⟧' =
    F.map e3 ≫ VZ ≫ R ≫ c
  calc
    _ = F.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) ≫
        (F.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).map e0) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom) :=
      congrArg (fun z => F.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) ≫ z) hp
    _ = F.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).map e0) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso.inv) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom :=
      congrArg (fun z => F.map z ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom) hc
    _ = F.map g ≫ (F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso.inv ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionObjectIso S X).hom) := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map g ≫ (F.map es ≫ V ≫ P ≫ c) :=
      congrArg (fun z => F.map g ≫ z) hv
    _ = F.map (g ≫ es) ≫ V ≫ P ≫ c := by
      rw [CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
    _ = F.map (e3 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.normalizedSemifreeCofiberConnectingToSuspension f) ≫ V ≫ P ≫ c :=
      congrArg (fun z => F.map z ≫ V ≫ P ≫ c) he
    _ = F.map e3 ≫ (F.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.normalizedSemifreeCofiberConnectingToSuspension f) ≫ V ≫ P ≫ c) := by
      rw [CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
    _ = F.map e3 ≫ (VZ ≫ R ≫ c) := congrArg (fun z => F.map e3 ≫ z) hi
    _ = _ := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
