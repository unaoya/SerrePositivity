module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingFaceRank
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank

/-!
# Ex pairing の正則性

概要：最小複雑度を自然数値の弱 rank とし、pairing の先行関係の整礎性を証明する。
方針：同次元の先行元を余次元一の面として表し、型 II の面の複雑度の減少を使う。
規約：Moss 2020 Theorem 22 の正則性。Mathlib WeakRankFunction に接続する。
使われ方：単位 X→Ex(X) の anodyne 性。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：最小複雑度は Ex pairing の自然数値の弱 rank 関数である。
方針：同次元の先行関係を面による表示に直し、面の複雑度の減少を適用する。
規約：Moss 2020 Theorem 22 の正則性の証明。
使われ方：先行関係の整礎性を導く。
-/
def exPairingWeakRank (X : SSet.{u}) : (exPairingCore X).WeakRankFunction ℕ where
  rank s := (exComplexityLevel X _ s.2.val).val
  lt := by
    intro ⟨n, s⟩ ⟨m, t⟩ ⟨hne, hlt⟩ hd
    change n = m at hd
    subst m
    have hst : s.val ≠ t.val := by
      intro he
      apply hne
      exact congrArg (Sigma.mk n) (Subtype.ext he)
    obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp hlt.le
    change SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 1) at f
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    change (SSet.ex.obj X).δ i (exPairingStep X n t.val) =
      (SSet.ex.obj X).δ (exComplexityLevel X _ s.val).succ (exPairingStep X n s.val) at he
    have he' : (SSet.ex.obj X).δ i (exPairingStep X n t.val) = s.val := by
      simpa only [exPairingStep, exExpansion_face] using he
    exact exPairingStep_face_rank_lt X n s.val t.val s.property t.property hst i he'

/--
概要：Ex pairing の核の先行関係は整礎である。
方針：自然数値の弱 rank 関数と properness を使う。
規約：Moss 2020 Theorem 22。
使われ方：全次元の pairing の正則性。
-/
instance exPairingCore_isRegular (X : SSet.{u}) : (exPairingCore X).IsRegular :=
  (exPairingWeakRank X).isRegular

/--
概要：単位の像に対する Ex pairing は正則である。
方針：核の正則性を Mathlib の pairing へ移す。
規約：Moss 2020 Theorem 22。
使われ方：単位の anodyne 性の導出。
-/
instance exPairing_isRegular (X : SSet.{u}) : (exPairing X).IsRegular := by
  change (exPairingCore X).pairing.IsRegular
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
