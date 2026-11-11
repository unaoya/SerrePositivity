module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismBoundaryHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension

/-!
概要：元実／絶対二胞体と指定三比較側面を一つの実 prism 全境界へ貼る。
方針：元境界ホモトピーの二端点を固定し、既存の積の和の pushout を使う。
規約：元二胞体・元全側面の全単体を保持。内部充填は主張しない。
使われ方：元全境界充填の同じ実入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元三側面を時刻を第一因子にして保持する同じ実族。
方針：元境界ホモトピーの因子だけを交換する。
規約：元の全単体を保持。使われ方：元 prism 全境界の側面。 -/
def dgOdotMilnorNuNullPrismTimeBoundary (j : Fin 2) :
    (Δ[1] : SSet.{u + 2}) ⊗ (boundary 2 : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫
    (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h

/-- 概要：同じ元側面族と元両二胞体は二端点の全共有境界で一致する。
方針：元境界ホモトピーの全二端点を既存の区間境界公式へ渡す。
規約：元二胞体を固定。使われ方：元 prism 全境界の貼り合わせ条件。 -/
lemma dgOdotMilnorNuNullPrismBoundary_compatible (j : Fin 2) :
    ((boundary 1).ι ▷ (boundary 2 : SSet.{u + 2})) ≫
        dgOdotMilnorNuNullPrismTimeBoundary R d h j =
      ((boundary 1 : SSet.{u + 2}) ◁ (boundary 2).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
          (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j))
          (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality]
  apply congrArg₂ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary 2 : SSet.{u + 2}) ≫
      (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫
        (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h₀
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary 2 : SSet.{u + 2}) ≫
      (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫
        (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h₁

/-- 概要：同じ元両二胞体と指定三側面を全て保持する実 prism 全境界。
方針：元端点整合式で既存の積の和の pushout に貼る。
規約：元全五面を変更しない。使われ方：指定全境界の内部充填への入口。 -/
def dgOdotMilnorNuNullPrismFullBoundary (j : Fin 2) :
    (Subcomplex.unionProd (boundary 1) (boundary 2) : SSet.{u + 2}) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  (Subcomplex.unionProd.isPushout (boundary 1) (boundary 2)).desc
    (dgOdotMilnorNuNullPrismTimeBoundary R d h j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
      (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j))
      (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)))
    (dgOdotMilnorNuNullPrismBoundary_compatible R d h j)

/-- 概要：実 prism 全境界は同じ元三側面の全族を厳密回収する。
方針：同じ pushout の元左入射の回収を使う。
規約：元全側面の等号。使われ方：全充填後の指定三側面の保持。 -/
lemma dgOdotMilnorNuNullPrismFullBoundary_side (j : Fin 2) :
    Subcomplex.unionProd.ι₁ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h j =
      dgOdotMilnorNuNullPrismTimeBoundary R d h j :=
  (Subcomplex.unionProd.isPushout (boundary 1) (boundary 2)).inl_desc _ _ _

/-- 概要：実 prism 全境界は同じ元実／絶対二胞体の全単体を厳密回収する。
方針：同じ pushout の元右入射の回収を使う。
規約：両元二胞体の等号。使われ方：全充填後の元二胞体の保持。 -/
lemma dgOdotMilnorNuNullPrismFullBoundary_ends (j : Fin 2) :
    Subcomplex.unionProd.ι₂ (boundary 1) (boundary 2) ≫
        dgOdotMilnorNuNullPrismFullBoundary R d h j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
        (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j))
        (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)) :=
  (Subcomplex.unionProd.isPushout (boundary 1) (boundary 2)).inr_desc _ _ _

end SerrePositivity.KST.SConstruction
