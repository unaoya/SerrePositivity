module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-! # dg nerve の dg 関手に対する関手性

概要：dg 関手から単体的写像を作り、恒等関手と合成を保つことを示す。
方針：単体の像が任意の添字の引き戻しと可換であることを三分岐で検証する。
規約：HA Construction 1.3.1.6。使われ方：導来 ∞ 圏の関手と充満部分圏の包含。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v w t

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {T : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- 概要：恒等 dg 関手による単体データの像は元のデータ。
方針：対象と Hom 複体の恒等写像を各成分で評価する。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の恒等写像の法則。 -/
lemma map_id {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) : s.map (DGFunctor.id D) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData (map_id)


/-- 概要：dg 関手の合成による像は二回の像に一致する。
方針：Hom 複体の chain map の合成を各斉次元で評価する。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の合成保存。 -/
lemma map_comp {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (F : DGFunctor A D E) (G : DGFunctor A E T) :
    s.map (DGFunctor.comp F G) = (s.map F).map G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData (map_comp)


/-- 概要：dg 関手による像は任意の単調写像による単体の引き戻しと可換。
方針：単射の場合は元の成分、潰れた辺は単位保存、それ以外は零の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の写像の自然性。 -/
lemma _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (F : DGFunctor A D E)
    (α : Fin (m + 1) →o Fin (n + 1)) : (s.pullback α).map F = (s.map F).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    change (F.map (s.obj (α a)) (s.obj (α b))).f k ((s.pullback α).hom J a b k hJ ha hb hk) =
      ((s.map F).pullback α).hom J a b k hJ ha hb hk
    by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      rfl
    · by_cases hc : J.card = 2
      · have hk0 : k = 0 := by omega
        subst hk0
        have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
          (by rw [ha]; exact J.isLeast_min' _) (by rw [hb]; exact J.isGreatest_max' _)
        have hleft := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_unit_of_heq F ((s.pullback α).hom J a b 0 hJ ha hb hk)
          (congrArg s.obj hab) (s.pullback_hom_of_collapsed_pair α J a b 0 hJ ha hb hk hi hc)
        have hright := (s.map F).pullback_hom_of_collapsed_pair α J a b 0 hJ ha hb hk hi hc
        exact eq_of_heq (hleft.trans hright.symm)
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
        exact map_zero _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor (map_pullback)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D E T : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- 概要：dg 関手は dg nerve の単体的写像を定める。
方針：各次元の単体の像を取り、添字の引き戻しとの可換性を自然性に使う。
規約：HA Construction 1.3.1.6。対象宇宙は Mathlib の nerve の写像と同じく共通の宇宙。
使われ方：導来 ∞ 圏の関手と充満部分圏の包含。 -/
def _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E where
  app _ := ↾fun s => s.map F
  naturality _ _ f := by
    ext s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.toSimplexData F f.unop.toOrderHom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor (map)


/-- 概要：dg nerve の写像は恒等 dg 関手を恒等写像へ送る。
方針：各次元の単体データの恒等写像の法則を使う。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の関手としての恒等則。 -/
lemma map_id : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := A) D) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) := by
  ext n s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact SimplexData.map_id s.toSimplexData

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve (map_id)


/-- 概要：dg nerve の写像は dg 関手の合成を単体的写像の合成へ送る。
方針：各次元の単体データの合成の法則を使う。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の関手としての合成則。 -/
lemma map_comp (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A E T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.DGFunctor.comp F G) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G := by
  ext n s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact SimplexData.map_comp s.toSimplexData F G

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve (map_comp)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve
