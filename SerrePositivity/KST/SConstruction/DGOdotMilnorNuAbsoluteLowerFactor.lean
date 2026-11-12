module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteLowerTerminal
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteEndpoints

/-!
概要：絶対下三角形の全 Hom を同じ固定 ν の零合成空間へ因子分解する。
方針：元共有対角からの終対象性を同じ端点等号で固定 ν へ輸送する。
規約：上下の元二単体の全 Hom を保持。使われ方：同じ絶対面の指定全境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "Tgt" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：絶対下三角形の完全関手圏を同じ固定 ν の完全関手圏へ輸送する。
方針：元の始点・終点の指定等号を使う。
規約：等号による同型。使われ方：全 Hom の終頂点性の輸送。 -/
def dgOdotMilnorNuAbsoluteLowerExactTransport :
    DGOdotMilnorNuAbsoluteLowerExactFunctors R d h ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1}) :=
  eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y : SSet.{u + 1}))
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 1) (dgOdotMilnorNuAbsoluteTriangle_target R d h 1))

instance nuAbsoluteLowerExactTransport_isIso :
    IsIso (dgOdotMilnorNuAbsoluteLowerExactTransport R d h) :=
  inferInstanceAs (IsIso (eqToHom _))

/-- 概要：同じ絶対下三角形の Hom 輸送は完全関手圏の同じ端点輸送と可換。
方針：等号による同型の core 像と既存の core 包含の自然性を使う。
規約：全単体の等号。使われ方：固定 ν の同じ零成分への制限。 -/
lemma dgOdotMilnorNuAbsoluteLowerHom_transport :
    dgOdotMilnorNuAbsoluteTriangleHom R d h 1 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι =
      dgOdotMilnorNuAbsoluteLowerHom R d h ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (DGOdotMilnorNuAbsoluteLowerExactFunctors R d h)).ι ≫
          dgOdotMilnorNuAbsoluteLowerExactTransport R d h := by
  let q := dgOdotMilnorNuAbsoluteLowerExactTransport R d h
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map q = eqToHom
      (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y)
        (dgOdotMilnorNuAbsoluteTriangle_source R d h 1)
        (dgOdotMilnorNuAbsoluteTriangle_target R d h 1)) :=
    eqToHom_map _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => dgOdotMilnorNuAbsoluteLowerHom R d h ≫ f)
      ((congrArg (fun f => f ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι) hm.symm).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι q)))

/-- 概要：固定 ν に輸送した絶対下三角形の全 Hom 頂点は終関手。
方針：元全像の終対象性を等号による同型で保つ。
規約：全ての元 Hom 零単体。使われ方：零合成空間への全因子分解。 -/
lemma dgOdotMilnorNuAbsoluteLowerFixedHom_vertex_isTerminal
    (a : (nerve DGOdotMilnorNuNullTrianglePath.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuAbsoluteTriangleHom R d h 1 ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) a) := by
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (a.obj 0) = a := ComposableArrows.ext₀ rfl
  have ht := (ha ▸ dgOdotMilnorNuAbsoluteLowerHom_path_isTerminal R d h (a.obj 0)).map_of_isIso
    (dgOdotMilnorNuAbsoluteLowerExactTransport R d h)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgOdotMilnorNuAbsoluteLowerHom_transport R d h) (Opposite.op ⦋0⦌)) a
  exact he.symm ▸ ht

/-- 概要：絶対下三角形の全 Hom を同じ固定 ν の零合成空間へ置く。
方針：元全像の終頂点性で同じ全 Hom 写像を制限する。
規約：元二胞体を置換しない。使われ方：上下二単体を保つ相対充填。 -/
def dgOdotMilnorNuAbsoluteLowerFactor :
    nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (dgOdotMilnorNuAbsoluteTriangleHom R d h 1 ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι)
    (dgOdotMilnorNuAbsoluteLowerFixedHom_vertex_isTerminal R d h)

/-- 概要：同じ下三角形の零成分因子分解は元実 Hom 作用を全単体で回収する。
方針：core 包含の単射性と同じ全像制限の包含式を使う。
規約：元の二単体の Hom 写像の等号。使われ方：実面の全指定境界の保持。 -/
lemma dgOdotMilnorNuAbsoluteLowerFactor_hom :
    dgOdotMilnorNuAbsoluteLowerFactor R d h ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuAbsoluteTriangleHom R d h 1 := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι).mp
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => dgOdotMilnorNuAbsoluteLowerFactor R d h ≫ f)
      (dgOdotMilnorNuNullCoherenceHom_inclusion R d h))

end SerrePositivity.KST.SConstruction
