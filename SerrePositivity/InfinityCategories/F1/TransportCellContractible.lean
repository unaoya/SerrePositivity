module

public import SerrePositivity.InfinityCategories.F1.TransportCellCoproduct

/-!
概要：各セルと各境界の表現空間の可縮性から相対骨格の次段の可縮性を得る。
方針：非交和と実際の付加の pushout の可縮性保存を続ける。
規約：セルの分類射を厳密に保ち抽象的な分解を仮定しない。
使われ方：標準単体と境界の次元帰納法から各有限骨格への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SSet.relativeCellComplexOfMono
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の任意の非交和の余錐で各項の表現空間の可縮性を頂点へ移す。
方針：標準の非交和との一意な同型と表現空間の反変性を使う。
規約：選択された非交和の表示に依存しない。
使われ方：Mathlib の実際のセル族への可縮性の移送。 -/
lemma transportWitnessCofan_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] {I : Type (u + 1)} {a : I → Over B}
    (c : Cofan a) (hc : IsColimit c)
    (h : ∀ i, IsContractibleKan
      ((transportWitnessPullbackFunctor p).obj (Opposite.op (a i)))) :
    IsContractibleKan ((transportWitnessPullbackFunctor p).obj (Opposite.op c.pt)) :=
  isContractibleKan_of_iso ((transportWitnessPullbackFunctor p).mapIso
    (hc.coconePointUniqueUpToIso (coproductIsCoproduct a)).op)
    (transportWitnessCoproduct_isContractibleKan p a h)

/-- 概要：各相対セル上で表現空間が可縮なら実際のセル族上でも可縮。
方針：底上のセルの非交和の普遍性を使う。
規約：セルの添字は全ての非退化な相対セル。
使われ方：セル付加の標準単体側の入力。 -/
lemma transportWitnessCellSimplexes_isContractibleKan {E A B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ B) (n : ℕ)
    (h : ∀ c : Cell i n, IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportCellSimplexFamily i n c)))) :
    IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportCellSimplexes i n))) :=
  transportWitnessCofan_isContractibleKan p (transportCellSimplexCofan i n)
    (transportCellSimplexCofan_isColimit i n) h

/-- 概要：各相対セルの境界上で表現空間が可縮なら実際の境界族上でも可縮。
方針：底上の境界の非交和の普遍性を使う。
規約：全ての境界の高次データを同時に扱う。
使われ方：セル付加の境界側の入力。 -/
lemma transportWitnessCellBoundaries_isContractibleKan {E A B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ B) (n : ℕ)
    (h : ∀ c : Cell i n, IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportCellBoundaryFamily i n c)))) :
    IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportCellBoundaries i n))) :=
  transportWitnessCofan_isContractibleKan p (transportCellBoundaryCofan i n)
    (transportCellBoundaryCofan_isColimit i n) h

/-- 概要：各セルと境界の可縮性から相対骨格の次段の可縮性を得る。
方針：二つのセル族の可縮性を実際のセル付加の pushout に渡す。
規約：前段の表現空間の可縮性も必要とする。
使われ方：有限骨格の次元帰納法の帰納段階。 -/
lemma transportWitnessRelativeSkeletonSucc_isContractibleKan {E A B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ B) (n : ℕ)
    (hprev : IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportRelativeSkeleton i n))))
    (hs : ∀ c : Cell i n, IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportCellSimplexFamily i n c))))
    (hb : ∀ c : Cell i n, IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportCellBoundaryFamily i n c)))) :
    IsContractibleKan ((transportWitnessPullbackFunctor p).obj
      (Opposite.op (transportRelativeSkeleton i (n + 1)))) :=
  transportWitnessPushout_isContractibleKan p (transportCellAttachment_isPushout i n)
    (transportWitnessCellBoundaries_isContractibleKan p i n hb)
    (transportWitnessCellSimplexes_isContractibleKan p i n hs) hprev

end SerrePositivity.InfinityCategories
