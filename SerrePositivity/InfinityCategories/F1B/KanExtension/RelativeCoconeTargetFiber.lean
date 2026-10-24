module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeFamilyInitial
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CartesianPullbackFst

/-!
概要：相対余錐制限の標的を元の図式へ射影し、その fiber を通常の余錐の族と同定する。
方針：第二成分の射影と定値な第一成分で同型の両方向を構成する。
規約：元の図式の像は p≫U とする。
使われ方：図式固定の相対普遍性を全余錐の相対制限へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対余錐制限の標的から元の図式への射影。
方針：引き戻しの第一射影を取る。
規約：元の D の図式を保持する。
使われ方：相対余錐制限を共通の図式圏の上の射として扱う。 -/
abbrev kanRelativeCoconeTargetProjection (K : SSet.{u}) {D E : SSet.{u}} (U : D ⟶ E) :
    KanRelativeCoconeTarget K U ⟶ (ihom K).obj D :=
  pullback.fst ((ihom K).map U) (coconeRestriction K E)

/-- 概要：相対余錐の標的の指定図式上の fiber は像の図式の余錐の族と同型。
方針：標的の余錐成分を取り、逆は元の図式の定値族と合わせる。
規約：U に充填性は仮定しない。
使われ方：全空間の相対比較と図式固定の後合成の同定。 -/
def kanRelativeCoconeTargetFiberIso {K D E : SSet.{u}} (p : K ⟶ D) (U : D ⟶ E) :
    vertexFiber (kanRelativeCoconeTargetProjection K U) (functorVertex p) ≅
      coconeFamily (p ≫ U) where
  hom := vertexFiberLift (coconeRestriction K E) (functorVertex (p ≫ U))
    (vertexFiberι (kanRelativeCoconeTargetProjection K U) (functorVertex p) ≫
      pullback.snd ((ihom K).map U) (coconeRestriction K E)) (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, vertexFiberι_comp,
          SSet.const_comp]
        rfl)
  inv := vertexFiberLift (kanRelativeCoconeTargetProjection K U) (functorVertex p)
    (pullback.lift (SSet.const (functorVertex p))
      (vertexFiberι (coconeRestriction K E) (functorVertex (p ≫ U))) (by
        rw [vertexFiberι_comp, SSet.const_comp]
        rfl)) (pullback.lift_fst _ _ _)
  hom_inv_id := by
    apply vertexFiber_hom_ext (kanRelativeCoconeTargetProjection K U) (functorVertex p)
    rw [Category.assoc, vertexFiberLift_ι, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, SSet.comp_const, vertexFiberι_comp]
    · rw [Category.assoc, pullback.lift_snd, vertexFiberLift_ι]
  inv_hom_id := by
    apply vertexFiber_hom_ext (coconeRestriction K E) (functorVertex (p ≫ U))
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, vertexFiberLift_ι,
      pullback.lift_snd, Category.id_comp]

/-- 概要：標的の fiber 同型は全空間の余錐成分を保つ。
方針：fiber への持ち上げと包含を合成する。
規約：厳密な射の等式。
使われ方：相対比較を fiber に制限した射の同定。 -/
lemma kanRelativeCoconeTargetFiberIso_hom_ι {K D E : SSet.{u}} (p : K ⟶ D) (U : D ⟶ E) :
    (kanRelativeCoconeTargetFiberIso p U).hom ≫
        vertexFiberι (coconeRestriction K E) (functorVertex (p ≫ U)) =
      vertexFiberι (kanRelativeCoconeTargetProjection K U) (functorVertex p) ≫
        pullback.snd ((ihom K).map U) (coconeRestriction K E) :=
  rfl

/-- 概要：全余錐の相対制限は各図式の fiber で余錐の族の後合成と一致する。
方針：標的の fiber の包含へ合成し、相対制限の第二成分の式を使う。
規約：始域の fiber は coconeFamily p そのもの。
使われ方：標準 U 余極限から得た境界充填を全空間の fiber へ渡す。 -/
lemma kanRelativeCoconeRestriction_fiber_comparison {K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) :
    vertexFiberMap (coconeRestriction K D) (kanRelativeCoconeTargetProjection K U)
        (kanRelativeCoconeRestriction K U) (kanRelativeCoconeRestriction_fst K U)
        (functorVertex p) ≫ (kanRelativeCoconeTargetFiberIso p U).hom =
      kanCoconeFamilyPostcomp p U := by
  apply vertexFiber_hom_ext (coconeRestriction K E) (functorVertex (p ≫ U))
  rw [Category.assoc, kanRelativeCoconeTargetFiberIso_hom_ι, ← Category.assoc,
    vertexFiberMap_ι, Category.assoc, kanRelativeCoconeRestriction_snd]
  exact (kanRelativeVertexFiberMap_ι (coconeRestriction K D) (coconeRestriction K E)
    ((ihom (join K (Δ[0] : SSet.{u}))).map U) ((ihom K).map U)
    ((pre (joinInl K (Δ[0] : SSet.{u}))).naturality U).symm (functorVertex p)).symm

end SerrePositivity.InfinityCategories.F1B
