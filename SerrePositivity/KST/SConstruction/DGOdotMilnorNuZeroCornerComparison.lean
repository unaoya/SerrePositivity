module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroCornerNullHom

/-!
概要：実零角と標準零角の指定比較に沿う元二短辺の完全関手比較。
方針：同じ fromZeroCategory を零角の成分とし、元左辺・元上辺を全零性で比較する。
規約：元零角・元上辺を変更しない。使われ方：上二胞体の混合 Hom 境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

/-- 概要：同じ実零化面の元左辺の固定 ν 完全射。
方針：同じ全対象商への射を固定 ν で写す。
規約：元の左辺。使われ方：零角の指定比較の実側。 -/
abbrev dgOdotMilnorNuZeroActualLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (K) (Z) :=
  dgKInputNuMap R (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))

/-- 概要：同じ実零化面の元上辺の固定 ν 完全射。
方針：元の全対象商延長を固定 ν で写す。
規約：元の上辺。使われ方：零角の指定比較の実側。 -/
abbrev dgOdotMilnorNuZeroActualTop : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Z) (B) :=
  dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))
local notation "t" => dgOdotMilnorNuZeroActualTop R d

/-- 概要：同じ標準零角から実零角への成分を経由する左辺。
方針：元核の toZeroCategory と同じ実零角への fromZeroCategory を合成する。
規約：零角成分は既指定のもの。使われ方：混合左面の終点。 -/
def dgOdotMilnorNuZeroComparisonLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (K) (Z) where
  hom := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K)).hom ≫ (fromZeroCategory (Z)).hom
  isExact := @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K)).isExact
    (fromZeroCategory (Z)).isExact

/-- 概要：同じ零角成分と元実上辺の合成。
方針：指定 fromZeroCategory と元上辺を合成する。
規約：元の実上辺。使われ方：混合上面の始点。 -/
def dgOdotMilnorNuZeroComparisonTop : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B) where
  hom := (fromZeroCategory (Z)).hom ≫ (t).hom
  isExact := @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ (fromZeroCategory (Z)).isExact (t).isExact

/-- 概要：元実左辺と零角の指定成分を経由する左辺の全関手同型。
方針：同じ実零角の全零性を両関手へ適用する。
規約：元の左辺と同じ零角成分。使われ方：混合左面の元 Hom 辺。 -/
def dgOdotMilnorNuZeroComparisonLeftIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorNuZeroActualLeft R d).hom (dgOdotMilnorNuZeroComparisonLeft R d).hom :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => dgFixedNullInput_isZeroCategory R _ _)
    (fun _ => dgFixedNullInput_isZeroCategory R _ _)

/-- 概要：指定零角成分後の元上辺と同じ絶対上辺の全関手同型。
方針：実零角の全零性と両完全射の零対象保存を使う。
規約：元二関手を保持。使われ方：混合上面の元 Hom 辺。 -/
def dgOdotMilnorNuZeroComparisonTopIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorNuZeroComparisonTop R d).hom (fromZeroCategory (B)).hom :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _
    (fun _ => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ (t).hom (t).isExact _
      (dgFixedNullInput_isZeroCategory R _ _))
    (fun x => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ (fromZeroCategory (B)).hom
      (fromZeroCategory (B)).isExact x (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero x))

local instance nuZeroComparisonLeftHom_kanComplex :
    KanComplex (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex (K) (Z)

local instance nuZeroComparisonTopHom_kanComplex :
    KanComplex (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)

/-- 概要：元実左辺から同じ指定零角成分を経由する左辺への実 Hom 辺。
方針：同じ全関手同型の core 像を実辺で表示する。
規約：元の両完全射を固定。使われ方：元上面の混合零 Hom 合成。 -/
def dgOdotMilnorNuZeroComparisonLeftEdge :
    (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)).Edge
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)
        (dgOdotMilnorNuZeroActualLeft R d))
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)
        (dgOdotMilnorNuZeroComparisonLeft R d)) :=
  Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (X := SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)) _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapCoreVertexIso (dgOdotMilnorNuZeroComparisonLeftIso R d)).hom).choose

/-- 概要：指定零角成分後の元上辺から同じ絶対上辺への実 Hom 辺。
方針：同じ全関手同型の core 像の実辺を取る。
規約：元の両完全射を固定。使われ方：元上面の混合零 Hom 合成。 -/
def dgOdotMilnorNuZeroComparisonTopEdge :
    (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)).Edge
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)
        (dgOdotMilnorNuZeroComparisonTop R d))
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)
        (fromZeroCategory (B))) :=
  Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (X := SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)) _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapCoreVertexIso (dgOdotMilnorNuZeroComparisonTopIso R d)).hom).choose

end SerrePositivity.KST.SConstruction
