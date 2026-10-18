module

public import SerrePositivity.KST.Comparison.LocalCoefficients
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# 局所係数の左 Kan 拡張の次数ごとの模型

概要：元の圏の忘却の左 Kan 拡張を、各次数の係数群の直和と同定する。
方針：点ごとの Kan 拡張の余極限について、各単体の恒等射への射を使う。
規約：Weibel K-book IV.1.6 の局所係数鎖複体を単体次数ごとに記述する。
使われ方：定数整数係数との比較とセル添付の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：指定次数の各単体の係数群の族。
方針：元の圏の対象に係数関手を評価する。
規約：局所定数性をまだ必要としない。
使われ方：次数ごとの直和の成分。
-/
def coefficientFiberFamily (X : SSet.{u}) (L : X.Elements ⥤ AddCommGrpCat.{u})
    (d : SimplexCategoryᵒᵖ) (x : X.obj d) : AddCommGrpCat.{u} :=
  L.obj (X.elementsMk d x)

/--
概要：点ごとの Kan 拡張の添字の終点に現れる単体。
方針：添字の射で元の単体を送る。
規約：忘却関手の余構造射の圏の対象。
使われ方：各成分を次数ごとの直和へ送る。
-/
def coefficientFiberEndpoint (X : SSet.{u}) (d : SimplexCategoryᵒᵖ)
    (a : CostructuredArrow (Functor.Elements.π X) d) : X.obj d :=
  X.map a.hom a.left.val

/--
概要：添字の元からその終点の単体への輸送の射。
方針：余構造射そのものを元の圏の射として使う。
規約：元の像の一致は定義から従う。
使われ方：Kan 拡張の余極限の余錐。
-/
def coefficientFiberTransport (X : SSet.{u}) (d : SimplexCategoryᵒᵖ)
    (a : CostructuredArrow (Functor.Elements.π X) d) :
    a.left ⟶ X.elementsMk d (coefficientFiberEndpoint X d a) :=
  { hom := a.hom, map_val := rfl }

/--
概要：余構造射の圏の射は終点の単体を変えない。
方針：余構造射の可換性と元の圏の像の一致を使う。
規約：全ての添字の射。
使われ方：次数ごとの直和への余錐の自然性。
-/
theorem coefficientFiberEndpoint_eq (X : SSet.{u}) (d : SimplexCategoryᵒᵖ)
    {a b : CostructuredArrow (Functor.Elements.π X) d} (h : a ⟶ b) :
    coefficientFiberEndpoint X d a = coefficientFiberEndpoint X d b := by
  change X.map a.hom a.left.val = X.map b.hom b.left.val
  rw [← h.w]
  simp only [Functor.Elements.π_map, CategoryTheory.Functor.map_comp, types_comp_apply]
  exact congrArg (fun z => X.map b.hom z) h.left.map_val

/--
概要：点ごとの Kan 拡張の図式から次数ごとの直和への余錐。
方針：各添字から終点への係数の輸送と、その直和への包含を合成する。
規約：局所定数性を仮定しない。
使われ方：係数鎖群の直和による表示。
-/
def coefficientFiberCocone (X : SSet.{u}) (L : X.Elements ⥤ AddCommGrpCat.{u})
    (d : SimplexCategoryᵒᵖ) :
    Cocone (CostructuredArrow.proj (Functor.Elements.π X) d ⋙ L) where
  pt := ∐ coefficientFiberFamily X L d
  ι := {
    app a := L.map (coefficientFiberTransport X d a) ≫
      Sigma.ι (coefficientFiberFamily X L d) (coefficientFiberEndpoint X d a)
    naturality := by
      intro a b h
      have he := coefficientFiberEndpoint_eq X d h
      have ht : coefficientFiberTransport X d a ≫
          eqToHom (congrArg (fun x => X.elementsMk d x) he) =
          h.left ≫ coefficientFiberTransport X d b := by
        apply Functor.Elements.Hom.ext
        have hh : (eqToHom (congrArg (fun x => X.elementsMk d x) he)).hom = 𝟙 d := by
          change (Functor.Elements.π X).map
            (eqToHom (congrArg (fun x => X.elementsMk d x) he)) = 𝟙 d
          rw [eqToHom_map]
          rfl
        have hw : a.hom = h.left.hom ≫ b.hom := h.w.symm
        simpa only [coefficientFiberTransport, Functor.Elements.comp_hom, hh,
          Category.comp_id] using hw
      dsimp
      rw [← Category.assoc, ← L.map_comp, ← ht, L.map_comp, Category.assoc]
      congr 1
      simp only [eqToHom_map]
      exact Sigma.eqToHom_comp_ι (coefficientFiberFamily X L d) he.symm }

/--
概要：恒等射を伴う単体の添字。
方針：指定次数の元を余構造射の圏の対象とする。
規約：各次数の直和の包含に対応する。
使われ方：次数ごとの余極限の普遍性。
-/
def coefficientFiberIdentity (X : SSet.{u}) (d : SimplexCategoryᵒᵖ) (x : X.obj d) :
    CostructuredArrow (Functor.Elements.π X) d :=
  CostructuredArrow.mk (Y := X.elementsMk d x) (𝟙 d)

/--
概要：恒等射の添字での余錐の射は直和の包含である。
方針：元の圏の恒等射の係数輸送を計算する。
規約：指定次数の全単体。
使われ方：余極限の一意性。
-/
theorem coefficientFiberCocone_identity (X : SSet.{u})
    (L : X.Elements ⥤ AddCommGrpCat.{u}) (d : SimplexCategoryᵒᵖ) (x : X.obj d) :
    (coefficientFiberCocone X L d).ι.app (coefficientFiberIdentity X d x) =
      Sigma.ι (coefficientFiberFamily X L d) x := by
  dsimp [coefficientFiberCocone, coefficientFiberIdentity]
  have he : coefficientFiberEndpoint X d (coefficientFiberIdentity X d x) = x := by
    simp [coefficientFiberEndpoint, coefficientFiberIdentity]
  have ht : coefficientFiberTransport X d (coefficientFiberIdentity X d x) =
      eqToHom (congrArg (fun y => X.elementsMk d y) he.symm) := by
    apply Functor.Elements.Hom.ext
    have hh : (eqToHom (congrArg (fun y => X.elementsMk d y) he.symm)).hom = 𝟙 d := by
      change (Functor.Elements.π X).map (eqToHom (congrArg (fun y => X.elementsMk d y) he.symm)) = _
      rw [eqToHom_map]
      rfl
    exact hh.symm
  change L.map (coefficientFiberTransport X d (coefficientFiberIdentity X d x)) ≫ _ = _
  rw [ht, eqToHom_map]
  exact Sigma.eqToHom_comp_ι (coefficientFiberFamily X L d) he

/--
概要：次数ごとの係数群の直和は点ごとの Kan 拡張の余極限である。
方針：各単体の恒等射から余極限の射を作り、全ての添字から恒等射への射で普遍性を示す。
規約：係数の輸送の可逆性さえ必要としない。
使われ方：正規化局所係数の鎖群の直和表示。
-/
def coefficientFiberIsColimit (X : SSet.{u}) (L : X.Elements ⥤ AddCommGrpCat.{u})
    (d : SimplexCategoryᵒᵖ) : IsColimit (coefficientFiberCocone X L d) where
  desc s := Sigma.desc (fun x => s.ι.app (coefficientFiberIdentity X d x))
  fac s a := by
    dsimp only [coefficientFiberCocone]
    rw [Category.assoc, Sigma.ι_comp_desc]
    let h : a ⟶ coefficientFiberIdentity X d (coefficientFiberEndpoint X d a) :=
      CostructuredArrow.homMk (coefficientFiberTransport X d a) (by
        change a.hom ≫ 𝟙 d = a.hom
        exact Category.comp_id _)
    exact s.w h
  uniq s m hm := by
    apply Sigma.hom_ext
    intro x
    rw [Sigma.ι_comp_desc, ← coefficientFiberCocone_identity X L d x]
    exact hm (coefficientFiberIdentity X d x)

/--
概要：係数の左 Kan 拡張の各次数は、その次数の単体の係数群の直和に同型である。
方針：点ごとの Kan 拡張の余極限表示を、構成した直和の余極限と比較する。
規約：任意の係数関手についての実際の同型。
使われ方：定数係数の自由群模型との比較。
-/
def coefficientSimplicialObjIsoSigma (X : SSet.{u}) (L : X.Elements ⥤ AddCommGrpCat.{u})
    (d : SimplexCategoryᵒᵖ) :
    ((coefficientSimplicialFunctor X).obj L).obj d ≅ ∐ coefficientFiberFamily X L d :=
  (Functor.Elements.π X).leftKanExtensionObjIsoColimit L d ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (coefficientFiberIsColimit X L d)

/--
概要：Kan 拡張の単位は直和表示で対応する単体の包含である。
方針：点ごとの Kan 拡張の標準余錐と、恒等射の添字を比較する。
規約：全ての次数と単体についての式。
使われ方：定数係数の自然な比較。
-/
@[reassoc] theorem coefficientSimplicialObjIsoSigma_unit (X : SSet.{u})
    (L : X.Elements ⥤ AddCommGrpCat.{u}) (d : SimplexCategoryᵒᵖ) (x : X.obj d) :
    ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
      (coefficientSimplicialObjIsoSigma X L d).hom =
        Sigma.ι (coefficientFiberFamily X L d) x := by
  have h := (Functor.Elements.π X).ι_leftKanExtensionObjIsoColimit_hom L d
    (coefficientFiberIdentity X d x)
  have h' : ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
      ((Functor.Elements.π X).leftKanExtensionObjIsoColimit L d).hom =
        colimit.ι (CostructuredArrow.proj (Functor.Elements.π X) d ⋙ L)
          (coefficientFiberIdentity X d x) := by
    change ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
      ((Functor.Elements.π X).leftKanExtension L).map (𝟙 d) ≫ _ = _ at h
    rw [((Functor.Elements.π X).leftKanExtension L).map_id d] at h
    have h0 : ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
        𝟙 (((Functor.Elements.π X).leftKanExtension L).obj d) ≫
          ((Functor.Elements.π X).leftKanExtensionObjIsoColimit L d).hom =
        ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
          ((Functor.Elements.π X).leftKanExtensionObjIsoColimit L d).hom :=
      congrArg (fun k => ((Functor.Elements.π X).leftKanExtensionUnit L).app
        (X.elementsMk d x) ≫ k) (Category.id_comp _)
    exact h0.symm.trans h
  dsimp only [coefficientSimplicialObjIsoSigma, Iso.trans_hom]
  rw [← Category.assoc, h']
  have hf : colimit.ι (CostructuredArrow.proj (Functor.Elements.π X) d ⋙ L)
      (coefficientFiberIdentity X d x) ≫
      ((colimit.isColimit _).coconePointUniqueUpToIso (coefficientFiberIsColimit X L d)).hom =
      (coefficientFiberCocone X L d).ι.app (coefficientFiberIdentity X d x) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  exact hf.trans (coefficientFiberCocone_identity X L d x)

end SerrePositivity.KST.Comparison
