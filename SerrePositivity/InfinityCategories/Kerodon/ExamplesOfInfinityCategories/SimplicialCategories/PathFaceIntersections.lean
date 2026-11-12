module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaces

/-!
# Path の零座標面の交わり

概要：二つの面の Hom 写像の合成は二つの零座標面の交わりと同型になる。
方針：部分単体集合の像と逆像、および thickening の関手性を使う。
規約：二つの除外点を j と j.succAbove k と書く。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の面上の Hom 写像の貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.SimplicialThickening
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {n : ℕ}
/-- 概要：零座標面の面写像に沿う逆像は対応する零座標面である。
方針：succAbove の像の所属と単射性を各 path で計算する。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
lemma pathAvoids_preimage_pathFaceMap (j : Fin (n + 2)) (k a b : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{w} (j.succAbove a))
      (b := ULift.up (j.succAbove b)) (ULift.up (j.succAbove k))).preimage
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a b) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up k) := by
  ext m F
  change (∀ t, ULift.up (j.succAbove k) ∉
    (SimplexCategory.δ j).toOrderHom.uliftMap '' (F.obj t).I) ↔
      ∀ t, ULift.up k ∉ (F.obj t).I
  constructor
  · intro h t hk
    exact h t ⟨ULift.up k, hk, rfl⟩
  · rintro h t ⟨x, hx, he⟩
    have he' : x = ULift.up k := by
      apply ULift.ext
      exact (Fin.strictMono_succAbove j).injective (congrArg ULift.down he)
    exact h t (he' ▸ hx)

/-- 概要：二つの面の合成が誘導する Path の Hom 写像を定義する。
方針：二つの native な面写像を合成する。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
def pathDoubleFaceMap (j : Fin (n + 3)) (k : Fin (n + 2)) (a b : Fin (n + 1)) :
    nerve (Path (ULift.up.{w} a) (ULift.up.{w} b)) ⟶
      nerve (Path (ULift.up.{w} (j.succAbove (k.succAbove a)))
        (ULift.up.{w} (j.succAbove (k.succAbove b)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap k a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j (k.succAbove a) (k.succAbove b)

/-- 概要：二つの面の合成の像は二つの零座標面の交わりである。
方針：零座標面の逆像と像の計算を用いる。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
lemma range_pathDoubleFaceMap (j : Fin (n + 3)) (k : Fin (n + 2))
    (a b : Fin (n + 1)) :
    SSet.Subcomplex.range (pathDoubleFaceMap.{w} j k a b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up (j.succAbove k)) := by
  rw [pathDoubleFaceMap, SSet.Subcomplex.range_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathFaceMap,
    ← pathAvoids_preimage_pathFaceMap j k (k.succAbove a) (k.succAbove b)]
  have hgen {X Y : SSet.{w}} (f : X ⟶ Y) (B : Y.Subcomplex) :
      (B.preimage f).image f = SSet.Subcomplex.range f ⊓ B := by
    ext m y
    change (∃ x, f.app m x ∈ B.obj m ∧ f.app m x = y) ↔
      ((∃ x, f.app m x = y) ∧ y ∈ B.obj m)
    aesop
  rw [hgen, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathFaceMap]

/-- 概要：二つの面の Hom 写像の合成は Mathlib の合成した順序写像の Hom 写像である。
方針：thickening の関手の合成則を Hom で評価する。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
lemma pathDoubleFaceMap_eq_native (j : Fin (n + 3)) (k : Fin (n + 2))
    (a b : Fin (n + 1)) :
    pathDoubleFaceMap.{w} j k a b =
      (SimplicialThickening.functor
        (SimplexCategory.δ k ≫ SimplexCategory.δ j).toOrderHom.uliftMap).map
          ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ := by
  change ((SimplicialThickening.functor (SimplexCategory.δ k).toOrderHom.uliftMap).comp SSet
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap)).map
      ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ = _
  apply eq_of_heq
  have hm (F G : EnrichedFunctor SSet
      (SimplicialThickening (ULift.{w} (Fin (n + 1))))
      (SimplicialThickening (ULift.{w} (Fin (n + 3))))) (h : F = G) :
      HEq (F.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) (G.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
    subst G
    rfl
  exact hm _ _ (SimplicialThickening.functor_comp
    (SimplexCategory.δ k).toOrderHom.uliftMap
    (SimplexCategory.δ j).toOrderHom.uliftMap).symm
/-- 概要：二つの面の Hom 写像の合成は単射である。
方針：両面の Hom 写像の単射性を合成する。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
lemma pathDoubleFaceMap_mono (j : Fin (n + 3)) (k : Fin (n + 2))
    (a b : Fin (n + 1)) : Mono (pathDoubleFaceMap.{w} j k a b) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap_mono.{w} k a b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap_mono.{w} j (k.succAbove a) (k.succAbove b)
  change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap k a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j (k.succAbove a) (k.succAbove b))
  infer_instance

/-- 概要：二つの零座標面の交わりを共通面の Path Hom と同型にする。
方針：二つの面の合成の単射性と像の等式を使う。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
noncomputable def pathDoubleFaceIso (j : Fin (n + 3)) (k : Fin (n + 2))
    (a b : Fin (n + 1)) :
    nerve (Path (ULift.up.{w} a) (ULift.up.{w} b)) ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up (j.succAbove (k.succAbove a)))
        (b := ULift.up (j.succAbove (k.succAbove b))) (ULift.up j) ⊓
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up (j.succAbove k)) :
            (nerve (Path (ULift.up (j.succAbove (k.succAbove a)))
              (ULift.up (j.succAbove (k.succAbove b))))).Subcomplex) := by
  letI := pathDoubleFaceMap_mono.{w} j k a b
  exact asIso (SSet.Subcomplex.toRange (pathDoubleFaceMap j k a b)) ≪≫
    SSet.Subcomplex.eqToIso (range_pathDoubleFaceMap j k a b)

/-- 概要：交わりとの同型と包含の合成は二つの面の合成になる。
方針：像への因子分解の定義を使う。
規約：除外する二点は j と j.succAbove k。ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
lemma pathDoubleFaceIso_hom_ι (j : Fin (n + 3)) (k : Fin (n + 2))
    (a b : Fin (n + 1)) :
    (pathDoubleFaceIso.{w} j k a b).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up (j.succAbove (k.succAbove a)))
        (b := ULift.up (j.succAbove (k.succAbove b))) (ULift.up j) ⊓
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up (j.succAbove k))).ι = pathDoubleFaceMap j k a b := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
