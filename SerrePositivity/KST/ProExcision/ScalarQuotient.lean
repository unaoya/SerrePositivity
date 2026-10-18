module

public import SerrePositivity.KST.ProExcision.ScalarConeHomology

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# スカラー商の関手性

概要：一変数比較を係数複体の射に自然な比較として扱う。
方針：線形写像をスカラー倍の像による商へ降ろし、cone 包含との可換性を使う。
規約：スカラーは固定。正則性・平坦性は要求しない。
使われ方：KST Lemma 4.10 の独立な冪指数と列長帰納法。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：a 倍の像で割る加群の商関手。
方針：線形写像のスカラーとの可換性で商写像を誘導する。
規約：a は固定。使われ方：KST Lemma 4.10 の短い列に対する pro 同型の商への保存。 -/
def scalarQuotientFunctor (a : R) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (M ⧸ (a • (LinearMap.id : M →ₗ[R] M)).range)
  map {M N} f := ModuleCat.ofHom (Submodule.mapQ _ _ f.hom (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f.hom x, (map_smul f.hom a x).symm⟩))
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- 概要：スカラー cone への包含は係数複体の射に自然。
方針：既存の cone 写像の右成分の計算を各次数へ適用する。
規約：複体の射の等式。使われ方：KST Lemma 4.10 の通常商の比較の自然性。 -/
@[reassoc] theorem scalarCone_inr_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    CochainComplex.mappingCone.inr (smulId a K) ≫ (scalarConeFunctor a).map f =
      f ≫ CochainComplex.mappingCone.inr (smulId a L) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact scalarConeFunctor_inr_map a f q

/-- 概要：ホモロジーの通常商から cone ホモロジーへの自然変換。
方針：商の代表元に持ち上げ、cone への包含の自然性をホモロジーへ写す。
規約：任意の次数 i。使われ方：KST Lemma 4.10 の二重塔の比較射。 -/
def scalarConeHomologyComparisonNatTrans (a : R) (i : ℤ) :
    homologyFunctor (ModuleCat.{u} R) (.up ℤ) i ⋙ scalarQuotientFunctor a ⟶
      scalarConeFunctor a ⋙ homologyFunctor _ _ i where
  app K := scalarConeHomologyComparison a K i
  naturality {K L} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have he := congrArg (homologyFunctor _ _ i).map (scalarCone_inr_naturality a f)
      simp only [Functor.map_comp] at he
      exact (congrArg (fun g ↦ g.hom x) he).symm

end SerrePositivity.KST.ProExcision
