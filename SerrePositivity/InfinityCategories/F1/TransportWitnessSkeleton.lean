module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessDescentFibrations
public import SerrePositivity.InfinityCategories.F1.TransportWitnessDescentLimits
public import SerrePositivity.InfinityCategories.F1.TransportWitnessIdentityPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
概要：底の骨格列に沿う表現空間の逆極限と遷移写像を構成する。
方針：単体集合の骨格余極限を底上の余極限へ移し表現の降下を適用する。
規約：第 n 段は次元が n 未満の単体で生成した部分複体。
使われ方：一般の底上の表現空間の可縮性の骨格帰納法。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 概要：底の骨格列を底上の圏の図式にする。
方針：骨格の包含を底への構造射として束ねる。
規約：第零段は空部分複体。
使われ方：表現空間の逆系の底の図式。 -/
def transportSkeletonOver (B : SSet.{u + 1}) : ℕ ⥤ Over B :=
  (B.skeleton.monotone.functor ⋙ Subcomplex.toSSetFunctor).toOver B
    (fun n ↦ (B.skeleton n).ι) (by intro i j f; rfl)

/-- 概要：骨格の包含から底の恒等射への余錐。
方針：各骨格の底への包含を底上の射として取る。
規約：余錐の頂点は底上の終対象の標準表示。
使われ方：表現空間の逆極限錐。 -/
def transportSkeletonOverCocone (B : SSet.{u + 1}) : Cocone (transportSkeletonOver B) where
  pt := Over.mk (𝟙 B)
  ι.app n := Over.homMk (B.skeleton n).ι (by
    change (B.skeleton n).ι ≫ 𝟙 B = (B.skeleton n).ι
    rw [Category.comp_id])
  ι.naturality i j f := by ext; rfl

/-- 概要：底上の骨格列の標準余錐は余極限。
方針：骨格の上限が全体であることを単体集合の余極限へ移す。
規約：骨格の添字は自然数。
使われ方：全ての骨格上の整合する表現から大域の表現を回収する。 -/
def transportSkeletonOverCocone_isColimit (B : SSet.{u + 1}) :
    IsColimit (transportSkeletonOverCocone B) := by
  apply isColimitOfReflects (Over.forget B)
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves Subcomplex.toSSetFunctor
      (CompleteLattice.colimitCocone B.skeleton.monotone.functor).isColimit)
    (Cocone.ext (Subcomplex.eqToIso B.iSup_skeleton ≪≫ Subcomplex.topIso B))

/-- 概要：底の骨格列に沿う表現の制限錐は厳密な逆極限。
方針：底上の骨格の余極限へ表現空間の降下を適用する。
規約：表現の存在や可縮性は仮定しない。
使われ方：一般の底上の可縮性を逆極限へ帰着する。 -/
def transportWitnessSkeletonCone_isLimit {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] :
    IsLimit (transportWitnessColimitCone p (transportSkeletonOverCocone B)) :=
  transportWitnessColimitCone_isLimit p _ (transportSkeletonOverCocone_isColimit B)

/-- 概要：骨格列の任意の包含に沿う表現の制限は Kan fibration。
方針：部分複体の包含の単射性を降下関手の射に適用する。
規約：隣接段に限らない。
使われ方：骨格逆系の fibration 条件。 -/
lemma transportWitnessSkeleton_map_fibration {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] {n m : ℕ} (f : n ⟶ m) :
    HomotopicalAlgebra.Fibration ((transportWitnessPullbackFunctor p).map
      ((transportSkeletonOver B).map f).op) := by
  have : Mono (((transportSkeletonOver B).map f).left) := by
    change Mono (Subcomplex.homOfLE (B.skeleton.monotone (leOfHom f)))
    infer_instance
  exact transportWitnessPullbackFunctor_map_fibration p _

/-- 概要：元の表現空間を頂点とする骨格への制限錐。
方針：恒等底変換の同型で既存の降下錐を前合成する。
規約：余分な pullback のモデルを錐の頂点に残さない。
使われ方：可縮性を元の表現空間へ移す。 -/
def transportWitnessSkeletonCone {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] :
    Cone ((transportSkeletonOver B).op ⋙ transportWitnessPullbackFunctor p) :=
  (transportWitnessColimitCone p (transportSkeletonOverCocone B)).extend
    (transportWitnessIdentityPullbackIso p).hom

/-- 概要：元の表現空間は骨格上の表現空間の厳密な逆極限。
方針：降下錐の極限性を恒等底変換の同型で移す。
規約：全次数の極限であり頂点集合だけの極限ではない。
使われ方：一般の底上の表現空間の可縮性の結論。 -/
def transportWitnessSkeletonCone_isLimit_actual {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] : IsLimit (transportWitnessSkeletonCone p) :=
  IsLimit.ofIsoLimit (transportWitnessSkeletonCone_isLimit p)
    ((transportWitnessColimitCone p (transportSkeletonOverCocone B)).extendIso
      (transportWitnessIdentityPullbackIso p).symm)

end SerrePositivity.InfinityCategories
