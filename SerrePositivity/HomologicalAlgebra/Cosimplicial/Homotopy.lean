module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Products.Basic

/-!
# 余単体ホモトピーから余鎖ホモトピーへ

## 概要
余単体対象のホモトピーを反対圏の単体ホモトピーとして扱い、交代余面複体に移す。

## 方針
交代余面と交代面の双対性を用い、Mathlib の単体ホモトピーを余鎖へ戻す。

## 規約
非正規化の交代余面複体を用いる。

## 使われ方
切断を持つ Čech 余脈体や pd de Rham の行の収縮。
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicTopology

namespace SerrePositivity.Cosimplicial

variable {C : Type*} [Category* C] [Preadditive C]

/-- 余単体写像間のホモトピーを反対圏の単体ホモトピーとして表す。 -/
abbrev CosimplicialHomotopy {X Y : CosimplicialObject C} (f g : X ⟶ Y) :=
  SimplicialObject.Homotopy ((cosimplicialSimplicialEquiv C).functor.map f.op) ((cosimplicialSimplicialEquiv C).functor.map g.op)

/-- 概要：交代余面複体と、反対圏の交代面複体を戻したものとの同型。
方針：各次数では恒等写像を用い、交代和の双対性を使う。
規約：鎖複体を反対圏から戻すと余鎖複体になる。
使われ方：余単体ホモトピーの余鎖ホモトピーへの移送。 -/
def cofaceComplexIsoUnop (X : CosimplicialObject C) :
    (alternatingCofaceMapComplex C).obj X ≅
      ((alternatingFaceMapComplex Cᵒᵖ).obj ((cosimplicialSimplicialEquiv C).functor.obj (op X))).unop :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro a b hab
    have hb : b = a + 1 := hab.symm
    subst b
    erw [Category.id_comp, Category.comp_id]
    change (((alternatingFaceMapComplex Cᵒᵖ).obj ((cosimplicialSimplicialEquiv C).functor.obj (op X))).d (a + 1) a).unop =
      ((alternatingCofaceMapComplex C).obj X).d a (a + 1)
    dsimp only [alternatingFaceMapComplex, alternatingCofaceMapComplex,
      AlternatingFaceMapComplex.obj, AlternatingCofaceMapComplex.obj, CochainComplex.of,
      ChainComplex.of]
    rw [ChainComplex.of_d, CochainComplex.of_d, AlternatingCofaceMapComplex.d_eq_unop_d])

/-- 概要：余単体ホモトピーは交代余面複体の余鎖ホモトピーを誘導する。
方針：単体ホモトピーから得られる鎖ホモトピーを反対圏から戻す。
規約：写像の向きは反対圏で二度反転する。
使われ方：Čech 余脈体の収縮。 -/
def CosimplicialHomotopy.toCochainHomotopy {X Y : CosimplicialObject C} {f g : X ⟶ Y}
    (h : CosimplicialHomotopy f g) :
    Homotopy ((alternatingCofaceMapComplex C).map f) ((alternatingCofaceMapComplex C).map g) := by
  let h' := (SimplicialObject.Homotopy.toChainHomotopy h).unop
  let h'' := (h'.compLeft (cofaceComplexIsoUnop X).hom).compRight (cofaceComplexIsoUnop Y).inv
  refine (Homotopy.ofEq ?_).trans (h''.trans (Homotopy.ofEq ?_))
  · ext n
    change f.app _ = (𝟙 _ ≫ f.app _) ≫ 𝟙 _
    simp
  · ext n
    change (𝟙 _ ≫ g.app _) ≫ 𝟙 _ = g.app _
    simp

/-- 概要：二つの余単体ホモトピーを項ごとの組にまとめる。
方針：反対圏の単体ホモトピーの各恒等式を成分ごとに確認する。
規約：積圏に値を取る余単体対象を用いる。
使われ方：二変数関手、特にテンソル積へのホモトピーの移送。 -/
def CosimplicialHomotopy.prod'
    {D : Type*} [Category* D] {X Y : CosimplicialObject C} {X' Y' : CosimplicialObject D}
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (h : CosimplicialHomotopy f g) (h' : CosimplicialHomotopy f' g') :
    CosimplicialHomotopy (NatTrans.prod' f f') (NatTrans.prod' g g') where
  h {n} i := Quiver.Hom.op (show (X.prod' X').obj (SimplexCategory.mk (n + 1)) ⟶
      (Y.prod' Y').obj (SimplexCategory.mk n) from ((h.h i).unop, (h'.h i).unop))
  h_zero_comp_δ_zero n := Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_zero_comp_δ_zero n))
      (congrArg Quiver.Hom.unop (h'.h_zero_comp_δ_zero n)))
  h_last_comp_δ_last n := Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_last_comp_δ_last n))
      (congrArg Quiver.Hom.unop (h'.h_last_comp_δ_last n)))
  h_succ_comp_δ_castSucc_of_lt i j hij :=
    Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_succ_comp_δ_castSucc_of_lt i j hij))
      (congrArg Quiver.Hom.unop (h'.h_succ_comp_δ_castSucc_of_lt i j hij)))
  h_succ_comp_δ_castSucc_succ j :=
    Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_succ_comp_δ_castSucc_succ j))
      (congrArg Quiver.Hom.unop (h'.h_succ_comp_δ_castSucc_succ j)))
  h_castSucc_comp_δ_succ_of_lt i j hji :=
    Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_castSucc_comp_δ_succ_of_lt i j hji))
      (congrArg Quiver.Hom.unop (h'.h_castSucc_comp_δ_succ_of_lt i j hji)))
  h_comp_σ_castSucc_of_le i j hij :=
    Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_comp_σ_castSucc_of_le i j hij))
      (congrArg Quiver.Hom.unop (h'.h_comp_σ_castSucc_of_le i j hij)))
  h_comp_σ_succ_of_lt i j hji :=
    Quiver.Hom.unop_inj (Prod.ext (congrArg Quiver.Hom.unop (h.h_comp_σ_succ_of_lt i j hji))
      (congrArg Quiver.Hom.unop (h'.h_comp_σ_succ_of_lt i j hji)))

/-- 余単体ホモトピーに定値ホモトピーを与える。 -/
def CosimplicialHomotopy.refl {X Y : CosimplicialObject C} (f : X ⟶ Y) :
    CosimplicialHomotopy f f :=
  SimplicialObject.Homotopy.refl _

/-- 項ごとの関手は余単体ホモトピーを保つ。 -/
def CosimplicialHomotopy.whiskerRight {D : Type*} [Category* D]
    {X Y : CosimplicialObject C} {f g : X ⟶ Y} (h : CosimplicialHomotopy f g) (F : C ⥤ D) :
    CosimplicialHomotopy (Functor.whiskerRight f F) (Functor.whiskerRight g F) :=
  SimplicialObject.Homotopy.whiskerRight h F.op

end SerrePositivity.Cosimplicial
