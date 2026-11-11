module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoFiveFactorCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoComparisonNaturalityTransfer

/-!
概要：元の全関手同型の指定成分と元の頂点同型の像の間の自然性を保持する。
方針：同じ関手同型のホモトピー圏の自然同型の自然性を使う。
規約：成分も頂点同型も選び直さない。使われ方：全 Hom の native 作用比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全関手同型の指定成分は、同じ元の頂点同型の像と可換な正方形をなす。 -/
lemma functorIso_app_vertexIso_naturality {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) {x y : X _⦋0⦌} (n : VertexIso x y) :
    VertexIso.map n f ≪≫ e.app y = e.app x ≪≫ VertexIso.map n g := by
  apply Iso.ext
  exact e.toNatIso.hom.naturality n.hom

/-- 同じ全関手同型の二成分で共役すると、同じ指定頂点同型の終域側の像に等しい。 -/
lemma functorIso_app_vertexIso_conjugation {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) {x y : X _⦋0⦌} (n : VertexIso x y) :
    (e.app x).symm ≪≫ VertexIso.map n f ≪≫ e.app y = VertexIso.map n g := by
  simpa only [Iso.trans_assoc] using
    iso_conjugation_of_naturality _ _ _ _ (functorIso_app_vertexIso_naturality e n)

/-- 同じ全関手同型の成分は、指定両端比較の正方形を通して移しても自然性を保つ。 -/
lemma functorIso_app_vertexIso_comparison_naturality {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) {x y : X _⦋0⦌} (n : VertexIso x y)
    {z w : Y _⦋0⦌} (ux : VertexIso (f.app _ x) z) (uy : VertexIso (f.app _ y) w)
    (m : VertexIso z w) (hu : ux ≪≫ m = VertexIso.map n f ≪≫ uy) :
    ((e.app x).symm ≪≫ ux) ≪≫ m = VertexIso.map n g ≪≫ ((e.app y).symm ≪≫ uy) := by
  exact iso_comparison_naturality_transfer _ _ _ _ _ _ _
    (functorIso_app_vertexIso_naturality e n) hu

/-- 同じ両端比較を用いた作用比較の逆も、同じ指定頂点同型と自然な正方形をなす。 -/
lemma functorIso_app_vertexIso_comparison_inverse_naturality {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) {x y : X _⦋0⦌} (n : VertexIso x y)
    {z w : Y _⦋0⦌} (ux : VertexIso (f.app _ x) z) (uy : VertexIso (f.app _ y) w)
    (m : VertexIso z w) (hu : ux ≪≫ m = VertexIso.map n f ≪≫ uy) :
    m ≪≫ ((e.app y).symm ≪≫ uy).symm =
      ((e.app x).symm ≪≫ ux).symm ≪≫ VertexIso.map n g := by
  exact (iso_inverse_exchange_of_square _ _ _ _
    (functorIso_app_vertexIso_comparison_naturality e n ux uy m hu).symm).symm

end SerrePositivity.InfinityCategories.F2
