module

public import SerrePositivity.KST.Comparison.LocalCoefficientOverFunctor
public import SerrePositivity.KST.Comparison.LocalCoefficientFibers
public import SerrePositivity.KST.Comparison.FiberCoefficientMaps

/-!
# 基底上の局所係数群の次数ごとの比較

概要：slice 圏の局所係数関手を、各次数で係数の直和の左随伴へ移す。
方針：Kan 拡張の単位と直和包含を比較し、基底点の等式の輸送を照合する。
規約：Weibel K-book IV.1.6。固定した基底の任意の局所係数系。
使われ方：局所係数の単射保存と余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：基底上の単体集合を指定次数の基底上の型へ評価する関手。
方針：単体次数への評価を slice 圏へ送る。
規約：基底も同じ次数で評価する。
使われ方：係数群の直和の関手との比較。
-/
def overSimplicialEvaluation (B : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    Over B ⥤ Over (B.obj d) :=
  Over.post (X := B) ((evaluation SimplexCategoryᵒᵖ (Type u)).obj d)

/--
概要：基底の指定次数の単体の係数群の族。
方針：局所係数を元の圏の対応する対象で評価する。
規約：微分や輸送をまだ取らない次数ごとの族。
使われ方：係数群の直和を取る左随伴の入力。
-/
def overSimplexCoefficientFamily {B : SSet.{u}} (L : LocalCoefficientSystem B)
    (d : SimplexCategoryᵒᵖ) (b : B.obj d) : AddCommGrpCat.{u} :=
  L.coefficients.obj (B.elementsMk d b)

/--
概要：Kan 拡張の直和表示の逆は各包含を単位へ送る。
方針：単位を保つ順方向の式へ比較同型の逆を合成する。
規約：任意の元の圏上の係数関手。
使われ方：次数ごとの比較の自然性の判定。
-/
@[reassoc] theorem coefficientSimplicialObjIsoSigma_inv_ι (X : SSet.{u})
    (L : X.Elements ⥤ AddCommGrpCat.{u}) (d : SimplexCategoryᵒᵖ) (x : X.obj d) :
    Sigma.ι (coefficientFiberFamily X L d) x ≫ (coefficientSimplicialObjIsoSigma X L d).inv =
      ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) := by
  let e := coefficientSimplicialObjIsoSigma X L d
  have h := coefficientSimplicialObjIsoSigma_unit X L d x
  calc
    _ = (((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫ e.hom) ≫
        e.inv := congrArg (fun q => q ≫ e.inv) h.symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/--
概要：基底上の係数輸送の成分は、基底点の等式による標準輸送に一致する。
方針：関手の等式の標準射を各単体で評価し、等式の証明の一意性を使う。
規約：固定した単体次数。
使われ方：係数群の直和の射との照合。
-/
theorem overLocalCoefficientSourceIso_app {B : SSet.{u}} (L : LocalCoefficientSystem B)
    {X Y : Over B} (f : X ⟶ Y) (d : SimplexCategoryᵒᵖ) (x : X.left.obj d) :
    (overLocalCoefficientSourceIso L f).hom.app (X.left.elementsMk d x) =
      eqToHom (congrArg (overSimplexCoefficientFamily L d)
        (overTypeMap_base ((overSimplicialEvaluation B d).map f) x).symm) := by
  dsimp only [overLocalCoefficientSourceIso, eqToIso.hom]
  rw [eqToHom_app]

/--
概要：局所係数の単体的群の指定次数と、基底上の型の係数の直和の自然同型。
方針：点ごとの Kan 拡張の直和表示を用い、単位との合成で自然性を証明する。
規約：基底との可換性による輸送も一致させる。
使われ方：局所係数の余極限保存。
-/
def overLocalCoefficientDegreeIso {B : SSet.{u}} (L : LocalCoefficientSystem B)
    (d : SimplexCategoryᵒᵖ) :
    overLocalCoefficientSimplicialFunctor L ⋙
        (evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{u}).obj d ≅
      overSimplicialEvaluation B d ⋙
        fiberCoefficientFunctor (B.obj d) (overSimplexCoefficientFamily L d) :=
  NatIso.ofComponents (fun X => coefficientSimplicialObjIsoSigma X.left
    (pullbackLocalCoefficients X.hom L).coefficients d) (by
    intro X Y f
    let LX := (pullbackLocalCoefficients X.hom L).coefficients
    let LY := (pullbackLocalCoefficients Y.hom L).coefficients
    let eX := coefficientSimplicialObjIsoSigma X.left LX d
    let eY := coefficientSimplicialObjIsoSigma Y.left LY d
    let a := (overLocalCoefficientSimplicialMap L f).app d
    let b := (fiberCoefficientFunctor (B.obj d) (overSimplexCoefficientFamily L d)).map
      ((overSimplicialEvaluation B d).map f)
    have h : eX.inv ≫ (a ≫ eY.hom) = b := by
      apply Sigma.hom_ext
      intro x
      let z := X.left.elementsMk d x
      let w := f.left.mapElements.obj z
      let uX := ((Functor.Elements.π X.left).leftKanExtensionUnit LX).app z
      let uY := ((Functor.Elements.π Y.left).leftKanExtensionUnit LY).app w
      let t := (overLocalCoefficientSourceIso L f).hom.app z
      let c := Sigma.ι (coefficientFiberFamily X.left LX d) x
      let c' := Sigma.ι (coefficientFiberFamily Y.left LY d) (f.left.app d x)
      let q := eqToHom (congrArg (overSimplexCoefficientFamily L d)
        (overTypeMap_base ((overSimplicialEvaluation B d).map f) x).symm)
      have hi : c ≫ eX.inv = uX := coefficientSimplicialObjIsoSigma_inv_ι _ _ _ x
      have hu : uX ≫ a = t ≫ uY := overLocalCoefficientSimplicialMap_unit L f z
      have hy : uY ≫ eY.hom = c' := coefficientSimplicialObjIsoSigma_unit _ _ _ _
      have ht : t = q := overLocalCoefficientSourceIso_app L f d x
      have hb : c ≫ b = q ≫ c' :=
        fiberCoefficientFunctor_map_ι (overSimplexCoefficientFamily L d)
          ((overSimplicialEvaluation B d).map f) x
      calc
        c ≫ (eX.inv ≫ (a ≫ eY.hom)) = (c ≫ eX.inv) ≫ (a ≫ eY.hom) :=
          (Category.assoc _ _ _).symm
        _ = uX ≫ (a ≫ eY.hom) := congrArg (fun r => r ≫ (a ≫ eY.hom)) hi
        _ = (uX ≫ a) ≫ eY.hom := (Category.assoc _ _ _).symm
        _ = (t ≫ uY) ≫ eY.hom := congrArg (fun r => r ≫ eY.hom) hu
        _ = t ≫ (uY ≫ eY.hom) := Category.assoc _ _ _
        _ = t ≫ c' := congrArg (fun r => t ≫ r) hy
        _ = q ≫ c' := congrArg (fun r => r ≫ c') ht
        _ = c ≫ b := hb.symm
    apply (cancel_epi eX.inv).mp
    change eX.inv ≫ (a ≫ eY.hom) = eX.inv ≫ (eX.hom ≫ b)
    exact h.trans (eX.inv_hom_id_assoc b).symm)

end SerrePositivity.KST.Comparison
