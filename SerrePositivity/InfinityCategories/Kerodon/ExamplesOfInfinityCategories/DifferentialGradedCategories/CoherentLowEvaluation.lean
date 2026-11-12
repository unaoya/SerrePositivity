module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComparison

/-!
# 零座標・一座標の Path の立方体評価

概要：内部座標が零個または一個なら、比較成分は唯一の旗の像の最上位成分である。
方針：零次・一次の置換が一つだけであることを使い、Path の旗の両端を計算する。
規約：一次の旗は内部点なしから内部点ありへ進み、追加の負号はない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の辺と三角形の一致。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：一点集合の唯一の内部座標を零番に番号付けする。
方針：Fin 1 と一点部分型の一意性を使う。
規約：唯一の番号付けなので降順の条件も満たす。
使われ方：Kerodon 2.5.9（Tag 00SC） の三角形の内部座標。 -/
def singletonEnumeration {T : Type u} [DecidableEq T] (t : T) :
    Fin 1 ≃ ↥({t} : Finset T) where
  toFun _ := ⟨t, Finset.mem_singleton_self t⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv z := Subtype.ext (Finset.mem_singleton.mp z.property).symm

/-- 概要：一つの内部点を加える Path の一次の旗。
方針：一点座標の立方体の唯一の最大旗を Path へ送る。
規約：向きは内部点なしから内部点あり。
使われ方：HA 1.3.1.16 の三角形の次数 −1 の成分。 -/
def singletonPathFlag (hab : a < b) (t : Set.Ioo a b) : (nerve (Path a b)) _⦋1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (singletonEnumeration t) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeFunctor hab {t}

/-- 概要：一点座標の旗の始点は内部点を含まない Path である。
方針：最大旗の零頂点は空集合であることを使う。
規約：両端点は Path が常に含む。
使われ方：Kerodon 2.5.9（Tag 00SC） の三角形の直接辺。 -/
lemma singletonPathFlag_obj_zero (hab : a < b) (t : Set.Ioo a b) :
    (singletonPathFlag hab t).obj 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab ∅ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab
    ((Subtype.val : ↥({t} : Finset _) → Set.Ioo a b) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (singletonEnumeration t)).obj 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_obj_zero, Set.image_empty]

/-- 概要：一点座標の旗の終点はその内部点を含む Path である。
方針：最大旗の最終頂点は全座標であり、一点部分型の像を計算する。
規約：内部点を加える向きの合成辺。
使われ方：HA 1.3.1.16 の三角形の二辺の合成に対応する端点。 -/
lemma singletonPathFlag_obj_one (hab : a < b) (t : Set.Ioo a b) :
    (singletonPathFlag hab t).obj 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab {t} := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab
    ((Subtype.val : ↥({t} : Finset _) → Set.Ioo a b) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (singletonEnumeration t)).obj (Fin.last 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_obj_last]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_singleton_iff]
  exact ⟨fun ⟨v, hv⟩ ↦ hv ▸ Finset.mem_singleton.mp v.property,
    fun hz ↦ ⟨⟨t, Finset.mem_singleton_self t⟩, hz.symm⟩⟩

/-- 概要：内部点のない比較成分は二端点だけの Path の零成分である。
方針：零次立方体の唯一の旗を定数の Path の零単体に同定する。
規約：符号は +1 で、次数は零。
使われ方：Kerodon 2.5.9（Tag 00SC） の比較写像が辺を保つことの検査。 -/
lemma coherentCubeComponent_empty
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D)) (hab : a < b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab ∅ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) (s.obj (.mk a)) (s.obj (.mk b)) 0
        ((s.map (.mk a) (.mk b)).app (Opposite.op ⦋0⦌)
          ((CategoryTheory.Functor.const (Fin 1)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab ∅))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (R := R) (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (∅ : Finset (Set.Ioo a b)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab ∅) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_zero]
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) (s.obj (.mk a)) (s.obj (.mk b)) 0)
  apply congrArg ((s.map (.mk a) (.mk b)).app _)
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  have ht : t = 0 := by exact Subsingleton.elim (α := Fin 1) _ _
  subst t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab
    ((Subtype.val : ↥(∅ : Finset (Set.Ioo a b)) → Set.Ioo a b) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration ∅)).obj 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_obj_zero, Set.image_empty]
  rfl

/-- 概要：内部点が一つの比較成分は内部点を加える Path の一次の旗の最上位成分である。
方針：唯一の降順番号付けによる一次立方体の評価の一項を取る。
規約：次数 −1、追加の符号なし。
使われ方：HA 1.3.1.16 の比較写像が三角形のホモトピー成分を保つことの検査。 -/
lemma coherentCubeComponentAt_singleton
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (t : Set.Ioo a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab {t} (-1) (by simp) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) (s.obj (.mk a)) (s.obj (.mk b)) 1
        ((s.map (.mk a) (.mk b)).app (Opposite.op ⦋1⦌) (singletonPathFlag hab t)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_eq_componentAt s hab (singletonEnumeration t)
    (Subsingleton.strictAnti _) (by simp)
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_one _ _)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
