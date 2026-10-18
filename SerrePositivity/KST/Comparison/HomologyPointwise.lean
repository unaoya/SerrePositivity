module

public import SerrePositivity.KST.Comparison.HomologyColimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.Algebra.Category.Grp.AB

/-!
# 関手圏のホモロジーと余極限

概要：アーベル群の図式の三項複体のホモロジーを次数ごとに比較する。
方針：評価関手の完全性を使い、余極限の完全性へ渡すための自然同型を構成する。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル濾過の極限段階。
使われ方：filtered colimit と整数ホモロジーの交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：図式の三項複体のホモロジーは点ごとのホモロジーに自然同型である。
方針：完全な評価関手によるホモロジー比較を各添字で束ねる。
規約：アーベル群値の任意の小さい図式。
使われ方：完全な余極限関手へのホモロジーの移送。
-/
def shortComplexPointwiseHomologyIso {J : Type u} [Category.{u} J]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) :
    S.homology ≅ (ShortComplex.functorEquivalence J AddCommGrpCat).functor.obj S ⋙
      ShortComplex.homologyFunctor AddCommGrpCat :=
  NatIso.ofComponents (fun j => (S.mapHomologyIso ((evaluation J AddCommGrpCat).obj j)).symm)
    (by
      intro j k f
      have h := NatTrans.app_homology ((evaluation J AddCommGrpCat).map f) S
      change S.homology.map f ≫ (S.mapHomologyIso ((evaluation J AddCommGrpCat).obj k)).inv =
        (S.mapHomologyIso ((evaluation J AddCommGrpCat).obj j)).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans ((evaluation J AddCommGrpCat).map f))
      have h' : S.homology.map f =
          (S.mapHomologyIso ((evaluation J AddCommGrpCat).obj j)).inv ≫
            ShortComplex.homologyMap (S.mapNatTrans ((evaluation J AddCommGrpCat).map f)) ≫
              (S.mapHomologyIso ((evaluation J AddCommGrpCat).obj k)).hom := h
      rw [h']
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/--
概要：図式の三項複体の余極限を、その三つの対象と射の余極限から作る余錐。
方針：余極限の標準包含を三成分に使う。
規約：ホモロジーをまだ取らない実際の三項複体。
使われ方：点ごとのホモロジーと余極限の比較。
-/
def shortComplexColimitCocone {J : Type u} [Category.{u} J]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) :
    Cocone ((ShortComplex.functorEquivalence J AddCommGrpCat).functor.obj S) where
  pt := S.map (colim : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  ι := {
    app j := ShortComplex.Hom.mk (colimit.ι S.X₁ j) (colimit.ι S.X₂ j) (colimit.ι S.X₃ j)
      (by
        change colimit.ι S.X₁ j ≫ colim.map S.f = S.f.app j ≫ colimit.ι S.X₂ j
        exact ι_colimMap S.f j)
      (by
        change colimit.ι S.X₂ j ≫ colim.map S.g = S.g.app j ≫ colimit.ι S.X₃ j
        exact ι_colimMap S.g j)
    naturality := by
      intro j k f
      apply ShortComplex.Hom.ext
      · change S.X₁.map f ≫ colimit.ι S.X₁ k = colimit.ι S.X₁ j ≫ 𝟙 _
        simpa only [Category.comp_id] using colimit.w S.X₁ f
      · change S.X₂.map f ≫ colimit.ι S.X₂ k = colimit.ι S.X₂ j ≫ 𝟙 _
        simpa only [Category.comp_id] using colimit.w S.X₂ f
      · change S.X₃.map f ≫ colimit.ι S.X₃ k = colimit.ι S.X₃ j ≫ 𝟙 _
        simpa only [Category.comp_id] using colimit.w S.X₃ f }

/--
概要：三つの対象の余極限から作った三項複体の余錐は余極限である。
方針：三つの射影で標準の余極限になることを確認する。
規約：アーベル群の任意の小さい図式。
使われ方：余極限関手のホモロジー保存と図式の余極限の接続。
-/
def shortComplexColimitIsColimit {J : Type u} [Category.{u} J]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) : IsColimit (shortComplexColimitCocone S) :=
  ShortComplex.isColimitOfIsColimitπ _
    (by change IsColimit (colimit.cocone S.X₁); exact colimit.isColimit S.X₁)
    (by change IsColimit (colimit.cocone S.X₂); exact colimit.isColimit S.X₂)
    (by change IsColimit (colimit.cocone S.X₃); exact colimit.isColimit S.X₃)

/--
概要：完全な余極限は三項複体のホモロジーと交換する。
方針：完全な余極限関手によるホモロジー比較と、点ごとのホモロジーの自然同型を合成する。
規約：完全性は Mathlib の HasExactColimitsOfShape で要求する。
使われ方：AB5 による filtered colimit のホモロジー計算。
-/
def shortComplexExactColimitHomologyIso {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) :
    (S.map (colim : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})).homology ≅
      colimit ((ShortComplex.functorEquivalence J AddCommGrpCat).functor.obj S ⋙
        ShortComplex.homologyFunctor AddCommGrpCat) :=
  S.mapHomologyIso colim ≪≫ colim.mapIso (shortComplexPointwiseHomologyIso S)

/--
概要：完全な余極限とホモロジーの比較は標準の包含を保つ。
方針：評価から余極限への自然変換のホモロジーの式を、点ごとの比較へ合成する。
規約：任意の完全な余極限の形。
使われ方：ホモロジー関手の余極限保存の普遍性。
-/
@[reassoc] theorem shortComplexExactColimitHomologyIso_ι {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) (j : J) :
    ShortComplex.homologyMap ((shortComplexColimitCocone S).ι.app j) ≫
      (shortComplexExactColimitHomologyIso S).hom =
        colimit.ι ((ShortComplex.functorEquivalence J AddCommGrpCat).functor.obj S ⋙
          ShortComplex.homologyFunctor AddCommGrpCat) j := by
  let E := S.mapHomologyIso ((evaluation J AddCommGrpCat).obj j)
  let Ec := S.mapHomologyIso (colim : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  let P := shortComplexPointwiseHomologyIso S
  let φ := (shortComplexColimitCocone S).ι.app j
  let D := (ShortComplex.functorEquivalence J AddCommGrpCat).functor.obj S ⋙
    ShortComplex.homologyFunctor AddCommGrpCat
  have hm : colimit.ι S.homology j =
      E.inv ≫ ShortComplex.homologyMap φ ≫ Ec.hom :=
    NatTrans.app_homology (colim.ι j) S
  have hf : ShortComplex.homologyMap φ ≫ Ec.hom = E.hom ≫ colimit.ι S.homology j := by
    calc
      _ = E.hom ≫ (E.inv ≫ ShortComplex.homologyMap φ ≫ Ec.hom) := by
        simp only [Iso.hom_inv_id_assoc]
      _ = _ := congrArg (fun q => E.hom ≫ q) hm.symm
  have hn : colimit.ι S.homology j ≫ colim.map P.hom =
      P.hom.app j ≫ colimit.ι D j := ι_colimMap P.hom j
  change ShortComplex.homologyMap φ ≫ (Ec.hom ≫ colim.map P.hom) = colimit.ι D j
  calc
    _ = (ShortComplex.homologyMap φ ≫ Ec.hom) ≫ colim.map P.hom :=
      (Category.assoc _ _ _).symm
    _ = (E.hom ≫ colimit.ι S.homology j) ≫ colim.map P.hom :=
      congrArg (fun q => q ≫ colim.map P.hom) hf
    _ = E.hom ≫ (P.hom.app j ≫ colimit.ι D j) := by rw [Category.assoc, hn]
    _ = colimit.ι D j := by
      change E.hom ≫ (E.inv ≫ colimit.ι D j) = colimit.ι D j
      exact Iso.hom_inv_id_assoc E _

/--
概要：完全な余極限の三項複体の余錐にホモロジーを施しても余極限である。
方針：標準の包含を保つ比較同型で、標準の余極限余錐から移す。
規約：余極限の普遍性を実際に構成する。
使われ方：filtered colimit に沿うホモロジーの保存。
-/
def shortComplexHomologyColimitIsColimit {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{u})) :
    IsColimit ((ShortComplex.homologyFunctor AddCommGrpCat).mapCocone
      (shortComplexColimitCocone S)) := by
  refine IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (shortComplexExactColimitHomologyIso S).symm ?_)
  intro j
  apply (cancel_mono (shortComplexExactColimitHomologyIso S).hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (shortComplexExactColimitHomologyIso_ι S j).symm

/--
概要：アーベル群の三項複体のホモロジー関手は完全な形の余極限を保存する。
方針：図式を関手圏の三項複体へ移し、構成したホモロジー余極限の普遍性を適用する。
規約：filtered な添字では AB5 が完全性を供給する。
使われ方：複体のホモロジーと filtered colimit の交換。
-/
instance shortComplexHomology_preservesExactColimits {J : Type u} [Category.{u} J]
    [HasExactColimitsOfShape J AddCommGrpCat.{u}] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor AddCommGrpCat.{u}) where
  preservesColimit {F} := by
    let e := ShortComplex.functorEquivalence J AddCommGrpCat.{u}
    let S := e.inverse.obj F
    have : PreservesColimit ((e.inverse ⋙ e.functor).obj F)
        (ShortComplex.homologyFunctor AddCommGrpCat) :=
      preservesColimit_of_preserves_colimit_cocone (shortComplexColimitIsColimit S)
        (shortComplexHomologyColimitIsColimit S)
    exact preservesColimit_of_iso_diagram (ShortComplex.homologyFunctor AddCommGrpCat)
      (e.counitIso.app F)

end SerrePositivity.KST.Comparison
