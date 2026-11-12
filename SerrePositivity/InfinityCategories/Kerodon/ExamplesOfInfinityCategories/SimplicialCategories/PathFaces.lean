module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceRetraction

/-!
# Path の面の像と零座標面

概要：Path の面写像を、除外頂点を通らない path の列の部分単体集合と同定する。
方針：各次数の部分集合の像と退化による逆像を計算し、像と単射性を証明する。
規約：Mathlib の native な豊穣 Hom の写像を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の空洞立方体の零座標面。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.SimplicialThickening
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type w} [LinearOrder J] {a b : J}
/-- 概要：指定した点を全ての頂点で避ける path の列の部分単体集合を定義する。
方針：制限後の全頂点も同じ点を避けることを使う。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
def pathAvoids (j : J) : (nerve (Path a b)).Subcomplex where
  obj _ := {F | ∀ t, j ∉ (F.obj t).I}
  map f _F h t := h (f.unop.toOrderHom t)
variable {n : ℕ}
/-- 概要：単体の一つの面が Path の Hom の間に誘導する写像を定義する。
方針：Mathlib の thickening の豊穣関手の Hom 写像を取る。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
def pathFaceMap (j : Fin (n + 2)) (a b : Fin (n + 1)) :
    nerve (Path (ULift.up.{w} a) (ULift.up.{w} b)) ⟶
      nerve (Path (ULift.up.{w} (j.succAbove a)) (ULift.up.{w} (j.succAbove b))) :=
  (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
    ⟨⟨a⟩⟩ ⟨⟨b⟩⟩
/-- 概要：面への埋め込み後の二端点の間の path を元の面へ戻す。
方針：部分集合の退化による像を取り、両端点を逆写像性で確認する。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
def pathFacePreimage (j : Fin (n + 2)) (a b : Fin (n + 1))
    (p : Path (ULift.up.{w} (j.succAbove a)) (ULift.up.{w} (j.succAbove b))) :
    Path (ULift.up.{w} a) (ULift.up.{w} b) where
  I := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom.uliftMap '' p.I
  left := ⟨_, p.left, ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_succAbove j a)⟩
  right := ⟨_, p.right, ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_succAbove j b)⟩
  left_le k hk := by
    rcases hk with ⟨x, hx, rfl⟩
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom.monotone (p.left_le x hx)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_succAbove j a) ▸ h
  le_right k hk := by
    rcases hk with ⟨x, hx, rfl⟩
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).toOrderHom.monotone (p.le_right x hx)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_succAbove j b) ▸ h
/-- 概要：面へ戻す操作は path の包含を保存する関手である。
方針：像が部分集合の包含を保存することを用いる。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
def pathFacePreimageFunctor (j : Fin (n + 2)) (a b : Fin (n + 1)) :
    Path (ULift.up.{w} (j.succAbove a)) (ULift.up.{w} (j.succAbove b)) ⥤
      Path (ULift.up.{w} a) (ULift.up.{w} b) where
  obj := pathFacePreimage j a b
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩
/-- 概要：Path の面写像の像は除外頂点を避ける列の部分単体集合に等しい。
方針：片側は succAbove の像、逆向きは各 path の部分集合を退化で引き戻す。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
lemma range_pathFaceMap (j : Fin (n + 2)) (a b : Fin (n + 1)) :
    SSet.Subcomplex.range (pathFaceMap.{w} j a b) = pathAvoids (ULift.up j) := by
  ext m F
  change (∃ z, (pathFaceMap j a b).app m z = F) ↔ ∀ t, ULift.up j ∉ (F.obj t).I
  constructor
  · rintro ⟨z, rfl⟩ t ⟨x, hx, he⟩
    exact Fin.succAbove_ne j x.down (congrArg ULift.down he)
  · intro h
    refine ⟨(nerveMap (pathFacePreimageFunctor j a b)).app m F, ?_⟩
    refine CategoryTheory.Functor.ext (fun t ↦ ?_)
    apply Path.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_ulift_image j (F.obj t).I (fun x hx he ↦ h t (ULift.ext he ▸ hx))
/-- 概要：Path の Hom の面写像は単射である。
方針：各次数で単体の対象を比較し、succAbove による部分集合の像の単射性を使う。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
lemma pathFaceMap_mono (j : Fin (n + 2)) (a b : Fin (n + 1)) :
    Mono (pathFaceMap.{w} j a b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  rw [mono_iff_injective]
  intro F G h
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Path.ext
  have ht := congrArg (fun z ↦ (z.obj t).I) h
  change (SimplexCategory.δ j).toOrderHom.uliftMap '' (F.obj t).I =
    (SimplexCategory.δ j).toOrderHom.uliftMap '' (G.obj t).I at ht
  apply (Set.image_injective.mpr ?_) ht
  intro x y he
  apply ULift.ext
  exact (Fin.strictMono_succAbove j).injective (congrArg ULift.down he)
/-- 概要：Path の面の Hom 単体集合を除外頂点を避ける部分単体集合と同型にする。
方針：単射をその像へ移し、像の等式を使う。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
noncomputable def pathFaceIso (j : Fin (n + 2)) (a b : Fin (n + 1)) :
    nerve (Path (ULift.up.{w} a) (ULift.up.{w} b)) ≅
      pathAvoids (a := ULift.up (j.succAbove a))
        (b := ULift.up (j.succAbove b)) (ULift.up j) := by
  letI := pathFaceMap_mono.{w} j a b
  exact asIso (SSet.Subcomplex.toRange (pathFaceMap j a b)) ≪≫
    SSet.Subcomplex.eqToIso (range_pathFaceMap j a b)
/-- 概要：面の Hom と零座標面の同型は元の面写像を回収する。
方針：像への因子分解と部分単体集合の包含の定義を使う。
規約：除外頂点は j、端点はその面の頂点 a,b。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面からの回収。 -/
lemma pathFaceIso_hom_ι (j : Fin (n + 2)) (a b : Fin (n + 1)) :
    (pathFaceIso.{w} j a b).hom ≫
      (pathAvoids (a := ULift.up (j.succAbove a))
        (b := ULift.up (j.succAbove b)) (ULift.up j)).ι = pathFaceMap j a b := by
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
