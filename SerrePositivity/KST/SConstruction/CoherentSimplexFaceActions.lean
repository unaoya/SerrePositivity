module
public import SerrePositivity.KST.SConstruction.CoherentSimplexArrows
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaces

/-! # 保存した coherent 面の全 Path 作用の回収
概要：実単体の指定面の等号から、元の面の全豊穣写像を依存等号で回収する。
方針：面の Path 再添字による豊穣前合成の定義を展開し、指定面の等号を使う。
規約：頂点や成分だけでなく全 Path と全次数の実写像を保つ。局所 Kan 性は不要。
使われ方：三入力 BF 四面体の保存三面を同じ実写像空間の全作用へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の指定面全体の等号は、面の全 Path の実豊穣作用を回収する。 -/
lemma coherentSimplexFaceMapping_heq {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌) (j : Fin (n + 2))
    (t : (SimplicialNerve C) _⦋n⦌) (ht : (SimplicialNerve C).δ j s = t)
    (a b : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} j a b ≫
      s.map (.mk (ULift.up (j.succAbove a))) (.mk (ULift.up (j.succAbove b))))
      (t.map (.mk (ULift.up a)) (.mk (ULift.up b))) := by
  subst t
  rfl

end SerrePositivity.KST.SConstruction
