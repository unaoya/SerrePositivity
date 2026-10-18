module

public import SerrePositivity.KST.Comparison.StableHatGLKan
public import SerrePositivity.KST.Spectra.FilteredPointedHomotopy

/-!
# 安定 ĜL のホモトピー類と rank の余極限

概要：安定 ĜL の実際のホモトピー類は有限 rank のホモトピー類の余極限である。
方針：添字の宇宙を揃え、台集合の実際の余極限に K-L9 の有限代表の比較を適用する。
規約：KST Lemma 2.13 の高次の安定化。π_n の余極限の定理は K-L9 から借りる。
使われ方：有限 rank の係数表示の自然同型を安定 rank へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits SSet

/--
概要：自然数の rank の添字を単体集合の値宇宙と揃える同値。
方針：AsSmall の既存の圏同値を使う。
規約：有限 rank の意味と順序射を保持する。
使われ方：K-L9 の filtered colimit の宇宙への接続。
-/
def liftedRankEquivalence : AsSmall.{u} ℕ ≌ ℕ :=
  (AsSmall.equiv.{0, 0, u} (C := ℕ)).symm

/--
概要：宇宙を持ち上げた rank の圏は filtered である。
方針：自然数の圏との同値で filtered 性を移す。
規約：値宇宙は任意。
使われ方：ホモトピー類の filtered colimit の定理。
-/
instance liftedRank_isFiltered : IsFiltered (AsSmall.{u} ℕ) :=
  IsFiltered.of_equivalence (AsSmall.equiv.{0, 0, u} (C := ℕ))

/--
概要：宇宙を揃えた有限 rank の単位基点付き ĜL の図式。
方針：rank の同値で既存の点付き順序列を前合成する。
規約：rank と各遷移射は既存のものを保つ。
使われ方：K-L9 のホモトピー類の図式の入力。
-/
def stableHatGLLiftedPointedDiagram (A : SimplicialObject RingCat.{u}) :
    AsSmall.{u} ℕ ⥤ PointedSimplicialSet.{u} :=
  liftedRankEquivalence.functor ⋙ (hatGLRankSequence A ⋙ monoidPointedFunctor)

/--
概要：有限 rank の各段の台集合は Kan である。
方針：単体的環の Kan 性と可逆成分の比較を供給する。
規約：追加の Kan 性の仮定は置かない。
使われ方：ホモトピー類の図式を形成する。
-/
instance stableHatGLLiftedPointedDiagram_kan (A : SimplicialObject RingCat.{u})
    (j : AsSmall.{u} ℕ) : KanComplex ((stableHatGLLiftedPointedDiagram A).obj j).right :=
  inferInstanceAs (KanComplex (hatGLSpace A (liftedRankEquivalence.functor.obj j)))

/--
概要：宇宙を揃えた有限 rank の図式から実際の安定 ĜL への cocone。
方針：既存の点付き cocone を同値で引き戻す。
規約：安定対象とその単位基点を保つ。
使われ方：有限 rank のホモトピー類から安定対象への cocone。
-/
def stableHatGLLiftedPointedCocone (A : SimplicialObject RingCat.{u}) :
    Cocone (stableHatGLLiftedPointedDiagram A) :=
  (stableHatGLPointedCocone A).whisker liftedRankEquivalence.functor

/--
概要：持ち上げた cocone の台集合は実際の余極限である。
方針：既証明の台集合の余極限の普遍性を添字の圏同値で移す。
規約：新たな安定対象を選び直さない。
使われ方：K-L9 の有限代表による比較。
-/
def stableHatGLLiftedPointedCocone_underlyingIsColimit (A : SimplicialObject RingCat.{u}) :
    IsColimit (PointedSimplicialSet.forget.mapCocone (stableHatGLLiftedPointedCocone A)) :=
  (stableHatGLPointedCocone_underlyingIsColimit A).whiskerEquivalence liftedRankEquivalence

/--
概要：持ち上げた cocone の安定対象の台集合は Kan。
方針：安定 ĜL の既証明の Kan 性を同じ台集合へ渡す。
規約：選ばれた基点は単位のままとする。
使われ方：安定対象の実際のホモトピー類。
-/
instance stableHatGLLiftedPointedCocone_kan (A : SimplicialObject RingCat.{u}) :
    KanComplex (stableHatGLLiftedPointedCocone A).pt.right :=
  inferInstanceAs (KanComplex (monoidSpace (stableHatGL A)))

/--
概要：安定 ĜL の全自然数次数のホモトピー類は有限 rank の類の余極限である。
方針：台集合の余極限に K-L9 の有限代表と関係の因子分解の定理を適用する。
規約：零次数も含む。群構造を輸送で新たに定義しない。
使われ方：有限 rank の係数群の比較を安定化する。
-/
def stableHatGLHomotopyIsColimit (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    IsColimit (Spectra.pointedHomotopyCocone (stableHatGLLiftedPointedCocone A) n) :=
  Spectra.pointedHomotopyIsColimit (stableHatGLLiftedPointedCocone A)
    (stableHatGLLiftedPointedCocone_underlyingIsColimit A) n

end SerrePositivity.KST.Comparison
