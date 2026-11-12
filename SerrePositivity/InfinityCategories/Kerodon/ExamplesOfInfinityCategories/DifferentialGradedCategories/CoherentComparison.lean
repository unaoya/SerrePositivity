module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentCollapsedPair
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentSimplexEquation

/-!
# Dold–Kan coherent nerve から dg nerve への比較写像

概要：降順の立方体評価による比較単体を全ての面・退化と可換な単体集合の射にまとめる。
方針：有限頂点集合上で単射な場合、潰れた二点集合、高次の非単射の場合を合わせる。
規約：対象はそのまま、合成は後の射を先に置く本リポジトリの規約を使う。
使われ方：HA 1.3.1.16–1.3.1.17、Kerodon 2.5.9（Tag 00SC） の dg nerve との比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：比較成分族は全ての単調写像による引き戻しと可換である。
方針：有限頂点集合上の単射性と濃度二での分岐を既存の三つの成分の等式で処理する。
規約：面だけでなく退化も含む。
使われ方：HA 1.3.1.16 の比較写像の自然性。 -/
lemma coherentSimplexData_pullback {m n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData ((SimplicialThickening.functor α.uliftMap).comp SSet s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    by_cases hi : Set.InjOn α (I : Set _)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_pullback_hom_of_inj s α I a b k hI ha hb hk hi
    · by_cases hc : I.card = 2
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_pullback_hom_of_collapsed_pair s α I a b k hI ha hb hk hi hc
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc

/-- 概要：実際の dg 比較単体は全ての単調写像による引き戻しと可換である。
方針：単体のデータ部分の自然性を使い、方程式の証明の一意性で単体の等式にする。
規約：dg 単体の方程式を追加の仮定として要求しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の比較写像の各次数の自然性。 -/
lemma coherentSimplex_pullback {m n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex ((SimplicialThickening.functor α.uliftMap).comp SSet s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact coherentSimplexData_pullback s α

/-- 概要：Dold–Kan の単体的圏の coherent nerve から dg nerve への比較写像。
方針：各次数で降順の立方体評価から作った dg 単体を取り、引き戻しの自然性を使う。
規約：係数環と対象の宇宙を独立に保ち、単体集合の宇宙は max u v。
使われ方：HA 1.3.1.16–1.3.1.17 の二つの ∞ 圏の比較。 -/
def coherentComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D where
  app _ := ↾fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro s
    exact coherentSimplex_pullback s f.unop.toOrderHom

/-- 概要：比較写像の各単体での値は立方体評価から構成した dg 単体である。
方針：比較写像の定義を評価する。
規約：自然性の証明の選択は単体の値を変えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の比較写像の低次成分の検査。 -/
lemma coherentComparison_app {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌) :
    coherentComparison.app _ s = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s := rfl

/-- 概要：比較写像は各頂点で元の豊穣関手の同じ対象を取る。
方針：比較単体の対象成分の定義を評価する。
規約：Fin の頂点番号を native な ULift の頂点へ持ち上げる。
使われ方：HA 1.3.1.17 の本質的全射性の対象上の比較。 -/
lemma coherentComparison_obj {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌) (a : Fin (n + 1)) :
    (coherentComparison.app _ s).obj a = s.obj (.mk (ULift.up a)) := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
