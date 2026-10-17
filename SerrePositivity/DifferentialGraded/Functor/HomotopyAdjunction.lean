module
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # dg関手の閉零随伴の主ホモトピー圏への降下

## 概要
dg関手の閉零随伴の主ホモトピー圏への降下。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]
  (L : DGFunctor A D E) (R : DGFunctor A E D) (adj : L.onClosed ⊣ R.onClosed)

/-- 閉零随伴の単位を境界商へ送る。 -/
def homotopyAdjunctionUnit : 𝟭 (HomotopyCategory A D) ⟶ L.onHomotopy ⋙ R.onHomotopy where
  app X := (toHomotopy A D).map (adj.unit.app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
    change (toHomotopy A D).map f ≫ (toHomotopy A D).map (adj.unit.app Y) =
      (toHomotopy A D).map (adj.unit.app X) ≫
        (toHomotopy A D).map (R.onClosed.map (L.onClosed.map f))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (toHomotopy A D).map (adj.unit.naturality f)

/-- 閉零随伴の余単位を境界商へ送る。 -/
def homotopyAdjunctionCounit : R.onHomotopy ⋙ L.onHomotopy ⟶ 𝟭 (HomotopyCategory A E) where
  app X := (toHomotopy A E).map (adj.counit.app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (toHomotopy A E).map_surjective f
    change (toHomotopy A E).map (L.onClosed.map (R.onClosed.map f)) ≫
      (toHomotopy A E).map (adj.counit.app Y) =
        (toHomotopy A E).map (adj.counit.app X) ≫ (toHomotopy A E).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (toHomotopy A E).map (adj.counit.naturality f)

lemma homotopyAdjunction_left_triangle (X : HomotopyCategory A D) :
    L.onHomotopy.map ((homotopyAdjunctionUnit L R adj).app X) ≫
      (homotopyAdjunctionCounit L R adj).app (L.onHomotopy.obj X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (toHomotopy A E).map (L.onClosed.map (adj.unit.app X)) ≫
    (toHomotopy A E).map (adj.counit.app (L.onClosed.obj X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp]
  exact (congrArg (toHomotopy A E).map (adj.left_triangle_components X)).trans
    ((toHomotopy A E).map_id _)

lemma homotopyAdjunction_right_triangle (X : HomotopyCategory A E) :
    (homotopyAdjunctionUnit L R adj).app (R.onHomotopy.obj X) ≫
      R.onHomotopy.map ((homotopyAdjunctionCounit L R adj).app X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (toHomotopy A D).map (adj.unit.app (R.onClosed.obj X)) ≫
    (toHomotopy A D).map (R.onClosed.map (adj.counit.app X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp]
  exact (congrArg (toHomotopy A D).map (adj.right_triangle_components X)).trans
    ((toHomotopy A D).map_id _)

/-- 二つのdg関手の閉零随伴は主ホモトピー圏の随伴を誘導する。 -/
def homotopyAdjunction : L.onHomotopy ⊣ R.onHomotopy :=
  Adjunction.mkOfUnitCounit {
    unit := homotopyAdjunctionUnit L R adj
    counit := homotopyAdjunctionCounit L R adj
    left_triangle := by
      apply NatTrans.ext
      funext X
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using
          homotopyAdjunction_left_triangle L R adj X
    right_triangle := by
      apply NatTrans.ext
      funext X
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using
          homotopyAdjunction_right_triangle L R adj X }

/-- 商へ送った実際の射について随伴Hom同値も商への関手と可換。 -/
lemma homotopyAdjunction_homEquiv_map (X : ClosedCategory A D) (Y : ClosedCategory A E)
    (f : L.onClosed.obj X ⟶ Y) :
    (homotopyAdjunction L R adj).homEquiv ((toHomotopy A D).obj X)
        ((toHomotopy A E).obj Y) ((toHomotopy A E).map f) =
      (toHomotopy A D).map (adj.homEquiv X Y f) := by
  rw [Adjunction.homEquiv_unit]
  change (toHomotopy A D).map (adj.unit.app X) ≫
    (toHomotopy A D).map (R.onClosed.map f) = _
  rw [← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.DGFunctor
