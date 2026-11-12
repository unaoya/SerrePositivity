module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleTerminal
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-!
概要：元上三角形の全 Hom を固定 ν の同じ零合成空間へ厳密に因子分解する。
方針：証明済みの元全像の終対象性を同じ端点等号で固定 ν へ輸送する。
規約：全単体と元二胞体を保持。使われ方：実面の指定全境界の相対充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "X₀" => dgOdotMilnorNuNullTriangleStableObject R d 0
local notation "X₂" => dgOdotMilnorNuNullTriangleStableObject R d 2
local notation "Src" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "Tgt" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

private lemma nullExactHomTransport {A B C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (h : A = C) (k : B = D) :
    eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} => SimplicialCategory.sHom X Y) h k) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι ≫
        eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} =>
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y : SSet.{u})) h k) := by
  subst C
  subst D
  exact (Category.id_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι).trans
    (Category.comp_id (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι).symm

/-- 概要：元両端の完全関手圏を同じ固定 ν の完全関手圏へ輸送する。
方針：元二単体の端点等号を同じ完全関手圏に適用する。
規約：等号による同型。使われ方：元全 Hom の終対象性の輸送。 -/
def dgOdotMilnorNuNullUpperExactTransport :
    DGOdotMilnorNuNullUpperExactFunctors R d ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1}) :=
  eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Y : SSet.{u + 1}))
    (dgOdotMilnorNuNullTriangle_source R d 0) (dgOdotMilnorNuNullTriangle_target R d 0))

instance nuNullUpperExactTransport_isIso : IsIso (dgOdotMilnorNuNullUpperExactTransport R d) :=
  inferInstanceAs (IsIso (eqToHom _))

/-- 概要：固定 ν 端点への全 Hom 輸送は元完全関手の同じ輸送を保つ。
方針：同じ端点等号に対する core 包含の可換式を使う。
規約：全単体の等号。使われ方：零成分の固定 ν 内での判定。 -/
lemma dgOdotMilnorNuNullUpperHom_transport :
    dgOdotMilnorNuNullTriangleHom R d 0 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι =
      dgOdotMilnorNuNullUpperHom R d ≫ dgOdotMilnorNuNullUpperHomInclusion R d ≫
        dgOdotMilnorNuNullUpperExactTransport R d :=
  (Category.assoc _ _ _).trans (congrArg (fun f => dgOdotMilnorNuNullUpperHom R d ≫ f)
    (nullExactHomTransport
      (dgOdotMilnorNuNullTriangle_source R d 0) (dgOdotMilnorNuNullTriangle_target R d 0)))

/-- 概要：固定 ν の元上三角形の全 Hom 頂点は同じ終関手の零成分に入る。
方針：元全像の終対象性を等号による同型で輸送する。
規約：任意の元 Hom 零単体。使われ方：同じ零合成空間への全因子分解。 -/
lemma dgOdotMilnorNuNullUpperFixedHom_vertex_isTerminal
    (a : (nerve DGOdotMilnorNuNullTrianglePath.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuNullTriangleHom R d 0 ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) a) := by
  have ht := (dgOdotMilnorNuNullUpperHom_vertex_isTerminal R d a).map_of_isIso
    (dgOdotMilnorNuNullUpperExactTransport R d)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgOdotMilnorNuNullUpperHom_transport R d) (Opposite.op ⦋0⦌)) a
  exact he.symm ▸ ht

/-- 概要：元上三角形の全 Hom を同じ固定 ν の零合成空間へ置く。
方針：元全像の終頂点性で同じ全 Hom 写像を制限する。
規約：元二胞体を置換しない。使われ方：指定面比較の全パラメータ充填。 -/
def dgOdotMilnorNuNullUpperFactor :
    nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (dgOdotMilnorNuNullTriangleHom R d 0 ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι)
    (dgOdotMilnorNuNullUpperFixedHom_vertex_isTerminal R d)

/-- 概要：同じ零成分への全因子分解は元の実 Hom 作用を全単体で回収する。
方針：core 包含の単射性と元持ち上げの包含式を使う。
規約：元の二単体の Hom 写像の等号。使われ方：固定 ν の実面の厳密保持。 -/
lemma dgOdotMilnorNuNullUpperFactor_hom (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    dgOdotMilnorNuNullUpperFactor R d ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuNullTriangleHom R d 0 := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι).mp
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => dgOdotMilnorNuNullUpperFactor R d ≫ f)
      (dgOdotMilnorNuNullCoherenceHom_inclusion R d h))

end SerrePositivity.KST.SConstruction
