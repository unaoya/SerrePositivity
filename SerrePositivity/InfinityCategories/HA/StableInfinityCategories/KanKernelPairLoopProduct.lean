module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairDiagonal

/-! # 自己引き戻しの連結成分上のループ積

概要：ループの合成を自己引き戻しの π₀ に移すと、対角が単位、交換が右逆元となり、可換正方形に自然。
方針：ループ比較の単射性で合成の結合則・自然性・単位と逆射の公式に帰着する。
規約：選んだ基点を固定した演算であり、空間の厳密な積写像は選ばない。使われ方：Hom の加法との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：自己引き戻しの連結成分にループの合成を移した二項演算。
方針：二つの成分をループ表示へ送り、合成を同値の逆で戻す。
規約：積の順序はホモトピー圏の合成の順序。使われ方：加法との比較の具体的な演算。 -/
def kanKernelPairLoopProduct {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a b : SSet.π₀ (pullback p p)) : SSet.π₀ (pullback p p) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e).symm
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e b)

/-- 概要：ループ表示は移した積を射の合成へ送る。
方針：同値とその逆の打ち消し。
規約：選択した基点は固定。使われ方：積の公理と自然性の計算。 -/
lemma kanKernelPairPiZeroLoopEquiv_product {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a b : SSet.π₀ (pullback p p)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e (kanKernelPairLoopProduct p hE e a b) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e b :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e).apply_symm_apply _

/-- 概要：移したループ積は結合的。
方針：ループ表示の単射性と射の合成の結合則を使う。
規約：π₀ 上の厳密な等号。使われ方：ループから得る演算の構造。 -/
lemma kanKernelPairLoopProduct_assoc {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a b c : SSet.π₀ (pullback p p)) :
    kanKernelPairLoopProduct p hE e (kanKernelPairLoopProduct p hE e a b) c =
      kanKernelPairLoopProduct p hE e a (kanKernelPairLoopProduct p hE e b c) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e).injective
  simp only [kanKernelPairPiZeroLoopEquiv_product, Category.assoc]

/-- 概要：対角の基点の成分はループ積の左単位。
方針：対角を恒等射として読み、ループ表示の単射性を使う。
規約：基点の対角の成分を明示する。使われ方：零射との比較のための単位公式。 -/
lemma kanKernelPairLoopProduct_diagonal_left {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a : SSet.π₀ (pullback p p)) :
    kanKernelPairLoopProduct p hE e
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairDiagonal p) (SSet.π₀.mk e)) a = a := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e).injective
  rw [kanKernelPairPiZeroLoopEquiv_product, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_diagonal, Category.id_comp]

/-- 概要：対角の基点の成分はループ積の右単位。
方針：対角を恒等射として読み、ループ表示の単射性を使う。
規約：左単位と同じ成分。使われ方：加法との比較に必要な両側単位。 -/
lemma kanKernelPairLoopProduct_diagonal_right {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a : SSet.π₀ (pullback p p)) :
    kanKernelPairLoopProduct p hE e a
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairDiagonal p) (SSet.π₀.mk e)) = a := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e).injective
  rw [kanKernelPairPiZeroLoopEquiv_product, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_diagonal, Category.comp_id]

/-- 概要：二成分交換は移したループ積に関する右逆元。
方針：交換との合成が恒等射となる公式と対角の公式を比較する。
規約：演算の可換性は仮定しない。使われ方：加法に同定した後の負号の判定。 -/
lemma kanKernelPairLoopProduct_swap {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a : SSet.π₀ (pullback p p)) :
    kanKernelPairLoopProduct p hE e a (SSet.mapπ₀ (pullbackSymmetry p p).hom a) =
      SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairDiagonal p) (SSet.π₀.mk e) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e).injective
  rw [kanKernelPairPiZeroLoopEquiv_product, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_comp_swap,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_diagonal]

/-- 概要：可換正方形で誘導した自己引き戻しの写像は移したループ積を保つ。
方針：ループ表示の自然性の三つの等式を、底の関手の合成保存と基点輸送で結ぶ。
規約：両全空間は可縮な Kan、両底は Kan、両射は Kan fibration。
使われ方：Hom の後合成に対する演算の自然性の空間側。 -/
lemma kanKernelPairLoopProduct_naturality
    {E B E' B' : SSet.{u}} [KanComplex E] [KanComplex B]
    [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) [Fibration p] (q : E' ⟶ B') [Fibration q]
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (hE' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E')
    (e : E _⦋0⦌) (a b : SSet.π₀ (pullback p p)) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap p q f g h) (kanKernelPairLoopProduct p hE e a b) =
      kanKernelPairLoopProduct q hE' (f.app (Opposite.op ⦋0⦌) e)
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap p q f g h) a)
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap p q f g h) b) := by
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap p q f g h
  let j := eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B'))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h e))
  let P := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e
  let Q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv q hE' (f.app (Opposite.op ⦋0⦌) e)
  have hn (c : SSet.π₀ (pullback p p)) :
      j ≫ Q (SSet.mapπ₀ k c) = (hoFunctor.map g).toFunctor.map (P c) ≫ j :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_naturality p q f g h hE hE' e c
  apply Q.injective
  rw [kanKernelPairPiZeroLoopEquiv_product]
  apply (cancel_epi j).1
  rw [hn, kanKernelPairPiZeroLoopEquiv_product, CategoryTheory.Functor.map_comp]
  rw [Category.assoc, ← hn b, ← Category.assoc, ← hn a, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
