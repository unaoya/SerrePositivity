module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FiberwiseFunctorEquiv

/-!
概要：局所形の自然変換が誘導する fiber ごとの関手の制限。
方針：各底単体で局所形の自然変換を前合成し、自然性で面・退化と整合させる。
規約：固定底上の実際の射。F と G に充填性は仮定しない。
使われ方：普遍余錐の族から図式の族への制限の大域的な構成。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：局所形の自然変換で各図式を制限する。
方針：各底図式上の自然変換の成分を前合成する。
規約：底の構造射は保つ。
使われ方：fiber ごとの関手の制限の単体ごとの作用。 -/
def fiberwiseFunctorPreSimplex {B T D : SSet.{u}} {F G : Over B ⥤ SSet.{u}}
    (α : F ⟶ G) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex G D T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D T := ⟨s.1, α.app (Over.mk s.1) ≫ s.2⟩

/-- 概要：局所形による制限はパラメータによる制限と可換。
方針：自然変換の自然性を局所図式へ後合成する。
規約：任意のパラメータの射。
使われ方：関手の制限を単体集合の射にまとめる。 -/
lemma fiberwiseFunctorPreSimplex_restrict {B T U D : SSet.{u}}
    {F G : Over B ⥤ SSet.{u}} (α : F ⟶ G) (i : T ⟶ U)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex G D U) :
    fiberwiseFunctorPreSimplex α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorRestrict G D i s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorRestrict F D i (fiberwiseFunctorPreSimplex α s) := by
  rcases s with ⟨σ, h⟩
  refine Sigma.ext (x := _) (y := _) rfl ?_
  apply heq_of_eq
  change α.app (Over.mk (i ≫ σ)) ≫
      G.map (Over.homMk i rfl : Over.mk (i ≫ σ) ⟶ Over.mk σ) ≫ h =
    F.map (Over.homMk i rfl : Over.mk (i ≫ σ) ⟶ Over.mk σ) ≫ α.app (Over.mk σ) ≫ h
  exact congrArg (fun q ↦ q ≫ h)
    (α.naturality (Over.homMk i rfl : Over.mk (i ≫ σ) ⟶ Over.mk σ)).symm

/-- 概要：局所形の自然変換から fiber ごとの関手の制限射を作る。
方針：単体ごとの前合成と自然性を使う。
規約：自然変換とは反変の向き。
使われ方：Lemma 7.3.4.5 の普遍余錐を図式へ制限する射 V。 -/
def fiberwiseFunctorPre {B D : SSet.{u}} {F G : Over B ⥤ SSet.{u}} (α : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor G D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D where
  app _ := ↾fiberwiseFunctorPreSimplex α
  naturality {m n} i := by
    apply ConcreteCategory.hom_ext
    intro s
    exact fiberwiseFunctorPreSimplex_restrict α (stdSimplex.map i.unop) s

/-- 概要：fiber ごとの関手の制限は底を保つ。
方針：各単体で底の構造射を忘れないことを使う。
規約：strict な射の等式。
使われ方：制限の持ち上げ問題を底上で扱う。 -/
lemma fiberwiseFunctorPre_projection {B D : SSet.{u}} {F G : Over B ⥤ SSet.{u}}
    (α : F ⟶ G) : fiberwiseFunctorPre (D := D) α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection G D := rfl

/-- 概要：全空間上の図式の制限と fiber ごとの関手の制限は一致する。
方針：各標準単体で自然変換の自然性を使う。
規約：F・G の余極限保存はこの向きの自然性には不要。
使われ方：局所図式を大域的な持ち上げに変換する際の制限の照合。 -/
lemma fiberwiseFunctorCurry_pre {B A D : SSet.{u}} {F G : Over B ⥤ SSet.{u}}
    (α : F ⟶ G) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex G D A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry F (fiberwiseFunctorPreSimplex α s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry G s ≫ fiberwiseFunctorPre α := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact (fiberwiseFunctorPreSimplex_restrict α (SSet.yonedaEquiv.symm x) s).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
