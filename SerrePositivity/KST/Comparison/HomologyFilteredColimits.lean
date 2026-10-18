module

public import SerrePositivity.KST.Comparison.HomologyPointwise
public import SerrePositivity.KST.Comparison.HomologyQuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# 整数ホモロジーと filtered colimit

概要：整数ホモロジーがアーベル群で完全な形の余極限を保存することを証明する。
方針：複体の三項複体への評価、完全な余極限とホモロジーの交換、正規化比較を使う。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル濾過。filtered な場合の完全性は AB5 から供給する。
使われ方：Kan 置換の順序余極限とセル添付の極限段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：鎖複体から指定次数の三項複体を取る関手は余極限を保存する。
方針：三つの対象への射影で評価関手の余極限保存に帰着する。
規約：非負次数のアーベル群値鎖複体。
使われ方：複体のホモロジー関手の余極限保存。
-/
instance integralShortComplexFunctor_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{u, u}
      (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n) where
  preservesColimitsOfShape {_J} _ := {
    preservesColimit {F} := {
      preserves {c} hc := by
        refine ⟨ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_⟩
        · exact isColimitOfPreserves
            (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ)
              ((ComplexShape.down ℕ).prev n)) hc
        · exact isColimitOfPreserves
            (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) n) hc
        · exact isColimitOfPreserves
            (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ)
              ((ComplexShape.down ℕ).next n)) hc } }

/--
概要：アーベル群値鎖複体のホモロジー関手は完全な形の余極限を保存する。
方針：三項複体への関手の余極限保存と、そのホモロジーの余極限保存を合成する。
規約：完全性の仮定は AB5 から供給できる。
使われ方：非正規化整数鎖複体のホモロジーの余極限。
-/
instance integralChainHomology_preservesExactColimits {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] (n : ℕ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n) :=
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso AddCommGrpCat (ComplexShape.down ℕ) n).symm

/--
概要：非正規化整数ホモロジーは完全な形の余極限を保存する。
方針：自由整数鎖複体と複体のホモロジー関手の余極限保存を合成する。
規約：全自然数次数。
使われ方：正規化整数ホモロジーへの比較。
-/
instance unnormalizedIntegralHomology_preservesExactColimits {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] (n : ℕ) :
    PreservesColimitsOfShape J (unnormalizedIntegralHomologyFunctor.{u} n) := by
  dsimp only [unnormalizedIntegralHomologyFunctor]
  infer_instance

/--
概要：正規化整数ホモロジーは完全な形の余極限を保存する。
方針：非正規化側の保存性を証明済みの自然な正規化比較で戻す。
規約：filtered colimit は AB5 により含まれる。
使われ方：horn 添付の極限段階。
-/
instance integralHomology_preservesExactColimits {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] (n : ℕ) :
    PreservesColimitsOfShape J (integralHomologyFunctor.{u} n) :=
  preservesColimitsOfShape_of_natIso (normalizationHomologyNatIso n).symm

/--
概要：整数ホモロジーと完全な形の余極限の実際の比較同型。
方針：証明済みの余極限保存から標準比較の逆を取る。
規約：各段階の整数ホモロジーと余極限の整数ホモロジーを結ぶ。
使われ方：filtered な図式の計算。
-/
def integralHomologyColimitIso {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] (F : J ⥤ SSet.{u}) (n : ℕ) :
    integralHomology (colimit F) n ≅ colimit (F ⋙ integralHomologyFunctor n) :=
  preservesColimitIso (integralHomologyFunctor n) F

/--
概要：余極限と整数ホモロジーの比較は図式の射に関して自然である。
方針：余極限保存の標準自然同型の自然性を適用する。
規約：各段階の誘導射と余極限の誘導射を実際に比較する。
使われ方：段階ごとのホモロジー同型を余極限へ移す。
-/
theorem integralHomologyColimitIso_naturality {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] {F G : J ⥤ SSet.{u}}
    (α : F ⟶ G) (n : ℕ) :
    integralHomologyMap (colim.map α) n ≫ (integralHomologyColimitIso G n).hom =
      (integralHomologyColimitIso F n).hom ≫
        colim.map (Functor.whiskerRight α (integralHomologyFunctor n)) :=
  (preservesColimitNatIso (integralHomologyFunctor n)).hom.naturality α

/--
概要：各段階の整数ホモロジー同型は完全な形の余極限でも同型を誘導する。
方針：各段階のホモロジー射の自然変換を同型にまとめ、自然な余極限比較で移す。
規約：全ての自然数次数での主張。
使われ方：horn 添付を繰り返す極限段階。
-/
theorem integralHomologyIsomorphism_colimit {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] {F G : J ⥤ SSet.{u}}
    (α : F ⟶ G) (hα : ∀ j, IntegralHomologyIsomorphism (α.app j)) :
    IntegralHomologyIsomorphism (colim.map α) := by
  intro n
  let β := Functor.whiskerRight α (integralHomologyFunctor n)
  have (j : J) : IsIso (β.app j) := hα j n
  have : IsIso β := NatIso.isIso_of_isIso_app β
  have h : integralHomologyMap (colim.map α) n =
      (integralHomologyColimitIso F n).hom ≫ colim.map β ≫
        (integralHomologyColimitIso G n).inv := by
    apply (cancel_mono (integralHomologyColimitIso G n).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact integralHomologyColimitIso_naturality α n
  rw [h]
  infer_instance

/--
概要：整数ホモロジーは filtered colimit と交換する。
方針：アーベル群の AB5 による完全性を一般の比較同型へ供給する。
規約：filtered colimit のホモロジー保存を仮定しない。
使われ方：Kan 置換とセル濾過の極限段階。
-/
def integralHomologyFilteredColimitIso {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ SSet.{u}) (n : ℕ) :
    integralHomology (colimit F) n ≅ colimit (F ⋙ integralHomologyFunctor n) :=
  integralHomologyColimitIso F n

end SerrePositivity.KST.Comparison
