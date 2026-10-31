module

public import SerrePositivity.KST.ProExcision.KoszulGraded
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

/-!
# 一項複体との全テンソルのホモロジー比較

概要：濾過区間と一項複体のホモロジーを具体的な係数加群へ比較する。
方針：mapping cone、ホモトピー圏のホモロジー、シフト、平坦テンソルの自然同型を合成する。
規約：通常の複体とホモロジーだけを使用する。
使われ方：KST Lemma 4.10 の cone 長完全列の係数比較。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：次数 a の一項複体との全テンソルを、点ごとのテンソルのシフトへ同定する。
方針：一項複体のシフト、全テンソルのシフト、零度の比較を合成する。
規約：シフトは -a。使われ方：KST Lemma 4.10 の初頁の次数計算。 -/
def singleTensorShiftIso (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M) K ≅
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K)⟦-a⟧ :=
  (cochainTensorFixedRight K).mapIso
    (((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-a) a 0 (by omega)).app M).symm ≪≫
    cochainTensorShiftLeft (cochainSingleZero M) K (-a) ≪≫
    (shiftFunctor _ (-a : ℤ)).mapIso (cochainTensorSingleLeftIso M K)

/-- 概要：平坦な左テンソル関手とホモロジーの自然同型。
方針：平坦性による完全性を短複体のホモロジーに適用する。
規約：係数 M は R 加群として平坦。使われ方：KST Lemma 4.10 の自由な Koszul 項。 -/
def flatLeftTensorHomologyIso (M : ModuleCat.{u} R) [Module.Flat R M] (q : ℤ) :
    (tensorLeft M).mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor _ _ q ≅
      homologyFunctor _ _ q ⋙ tensorLeft M := by
  let : (tensorLeft M).PreservesHomology := Functor.preservesHomologyOfExact _
  exact NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso (tensorLeft M))
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ _ q).map f) (tensorLeft M))

/-- 概要：平坦な一項複体のテンソルのホモロジーは、係数とシフトしたホモロジーのテンソル。
方針：全テンソルのシフト比較と平坦テンソルのホモロジー保存を合成する。
規約：次数 q は q-a に移る。使われ方：KST Lemma 4.10 の初頁の項。 -/
def singleTensorHomologyIso (M : ModuleCat.{u} R) [Module.Flat R M]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a q : ℤ) :
    (cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M) K).homology q ≅
      (tensorLeft M).obj (K.homology (q - a)) :=
  (homologyFunctor _ _ q).mapIso (singleTensorShiftIso M K a) ≪≫
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R)
      (-a) q (q - a) (by omega)).app _) ≪≫
    (flatLeftTensorHomologyIso M (q - a)).app K

/-- 概要：切り詰めの下端の等しい表示はテンソル cone の同型を与える。
方針：添字の等式で置換し、恒等同型を取る。
規約：依存する射の型の変更を同型として明示する。使われ方：有限濾過の添字の正規化。 -/
def truncationTensorConeIsoOfEq (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b a' b' : ℤ) (h : b ≤ a) (h' : b' ≤ a') (ha : a = a') (hb : b = b') :
    CochainComplex.mappingCone ((tensorRight K).map (truncationInclusion P a b h)) ≅
      CochainComplex.mappingCone ((tensorRight K).map (truncationInclusion P a' b' h')) := by
  subst a'
  subst b'
  exact Iso.refl _


end SerrePositivity.KST.ProExcision
