module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorFiber

/-!
概要：混合評価の恒等変換と、固定成分の前合成を元の通常の射で読む。
方針：QCat の core の零単体の定義を計算し、全次数の定値族を比較する。
規約：元の輸送射と Hom の作用そのものを使う。
使われ方：第一三角形の同時刻 Hom と対角を指定三角形と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- QCat の通常の射の core 頂点は、同じ射の関手頂点を元の値とする。 -/
lemma qCatHomVertex_val (A B : QCat.{u}) (f : A ⟶ B) :
    (SimplicialCategory.homEquiv' A B f).val = functorVertex f := rfl

/-- 元の core の前合成の頂点は、同じ通常の射の合成を表す。 -/
lemma qCatHomVertex_pre (A B D : QCat.{u}) (f : A ⟶ B) (k : B ⟶ D) :
    (quasicategoryCoreMap ((pre (show A.obj ⟶ B.obj from f)).app D.obj)).app
        (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' B D k) =
      SimplicialCategory.homEquiv' A D (f ≫ k) := by
  apply Subtype.ext
  rfl

/-- 恒等変換の混合評価は、元の輸送射の core 頂点に全次数で定値。 -/
lemma cocartesianTransportDiagramMixedHom_identity
    {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d)
    (F : CocartesianTransportDiagramCategory C) :
    eId SSet F ≫ cocartesianTransportDiagramMixedHom f F F =
      SSet.const (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue F d) (F.val.map f)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
