module

public import SerrePositivity.KST.Comparison.MonoidComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 群状モノイドの平行移動

概要：単体的モノイドの頂点による平行移動を実単体的写像として構成する。
方針：誘導乗法と頂点の定数写像を使い、辺に沿う変化をホモトピーで制御する。
規約：Segal 1974 Proposition 1.5・1.6 の作用の比較。各次数の逆元は使わない。
使われ方：群状性から bar の作用写像のホモトピー可逆性を導く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

local instance (M : SimplicialObject MonCat.{u}) (n : SimplexCategoryᵒᵖ) :
    Monoid ((monoidSpace M).obj n) := inferInstanceAs (Monoid (M.obj n))

/--
概要：単体的モノイドの乗法を単体集合の写像として公開する。
方針：各次数の乗法を使い、準同型性から自然性を示す。
規約：Segal 1974 Proposition 1.5。非可換の順序を保つ。
使われ方：平行移動とそのホモトピー。
-/
def monoidMultiplication (M : SimplicialObject MonCat.{u}) :
    monoidSpace M ⊗ monoidSpace M ⟶ monoidSpace M where
  app n := TypeCat.ofHom (fun p => (p.1 : M.obj n) * p.2)
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (map_mul (M.map f).hom p.1 p.2).symm

/--
概要：頂点による左平行移動。
方針：頂点の定数写像と恒等写像を組にして乗法へ送る。
規約：Segal 1974 Proposition 1.6 の作用の面写像。
使われ方：群状性によるホモトピー可逆性。
-/
def monoidLeftTranslation (M : SimplicialObject MonCat.{u}) (a : M.obj (op ⦋0⦌)) :
    monoidSpace M ⟶ monoidSpace M :=
  lift (SSet.const a) (𝟙 (monoidSpace M)) ≫ monoidMultiplication M

/--
概要：単位元による平行移動は恒等写像である。
方針：全単体次数で準同型の単位保存と単位律を使う。
規約：Segal 1974 Proposition 1.5 の単位作用。
使われ方：平行移動の逆射の構成。
-/
theorem monoidLeftTranslation_one (M : SimplicialObject MonCat.{u}) :
    monoidLeftTranslation M 1 = 𝟙 (monoidSpace M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change M.obj n at x
  change (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom 1 * x = x
  rw [map_one, one_mul]

/--
概要：二つの左平行移動の合成を頂点の積で表す。
方針：単体作用の積の保存と結合律を全次数で使う。
規約：先に a、後に b を作用させる合成は b*a による平行移動。
使われ方：Segal 1974 Proposition 1.5 の群状性の利用。
-/
theorem monoidLeftTranslation_comp (M : SimplicialObject MonCat.{u})
    (a b : M.obj (op ⦋0⦌)) :
    monoidLeftTranslation M a ≫ monoidLeftTranslation M b = monoidLeftTranslation M (b * a) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change M.obj n at x
  change (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom b *
    ((M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom a * x) =
    (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom (b * a) * x
  rw [map_mul, mul_assoc]
/--
概要：辺で結ばれた頂点の左平行移動の間の実単体的ホモトピー。
方針：区間の座標を辺へ送り、残りの座標との積を取る。
規約：Segal 1974 Proposition 1.5・1.6。辺の逆向きの存在を仮定しない。
使われ方：平行移動が連結成分だけに依存すること。
-/
noncomputable def monoidLeftTranslationHomotopy (M : SimplicialObject MonCat.{u})
    {a b : M.obj (op ⦋0⦌)} (e : (monoidSpace M).Edge a b) :
    SSet.Homotopy (monoidLeftTranslation M a) (monoidLeftTranslation M b) where
  h := lift (snd _ _ ≫ SSet.yonedaEquiv.symm e.edge) (fst _ _) ≫ monoidMultiplication M
  h₀ := by
    dsimp only [monoidLeftTranslation]
    rw [← Category.assoc, comp_lift]
    simp only [SSet.ι₀_snd_assoc, SSet.ι₀_fst, SSet.const_comp]
    congr 2
    apply congrArg (SSet.const (X := monoidSpace M))
    rw [SSet.yonedaEquiv_symm_app]
    have hδ : SSet.stdSimplex.objEquiv (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        SimplexCategory.δ (1 : Fin 2) := by
      ext i
      fin_cases i
      rfl
    rw [hδ]
    exact e.src_eq
  h₁ := by
    dsimp only [monoidLeftTranslation]
    rw [← Category.assoc, comp_lift]
    simp only [SSet.ι₁_snd_assoc, SSet.ι₁_fst, SSet.const_comp]
    congr 2
    apply congrArg (SSet.const (X := monoidSpace M))
    rw [SSet.yonedaEquiv_symm_app]
    have hδ : SSet.stdSimplex.objEquiv (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SimplexCategory.δ (0 : Fin 2) := by
      ext i
      fin_cases i
      rfl
    rw [hδ]
    exact e.tgt_eq
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/--
概要：ホモトピーを同一視する関手の下では平行移動は成分だけに依存する。
方針：辺が与える実ホモトピーを使い、Mathlib の π₀ の商へ降ろす。
規約：Segal 1974 Proposition 1.5・1.6。関手のホモトピー不変性を明示する。
使われ方：anodyne 局所化の下での平行移動の可逆性。
-/
def monoidTranslationClass (M : SimplicialObject MonCat.{u})
    {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
    (hL : ∀ {f g : monoidSpace M ⟶ monoidSpace M}, SSet.Homotopy f g → L.map f = L.map g) :
    SSet.π₀ (monoidSpace M) → (L.obj (monoidSpace M) ⟶ L.obj (monoidSpace M)) :=
  SSet.π₀.lift (fun a => L.map (monoidLeftTranslation M a))
    (fun {_ _} e => hL (monoidLeftTranslationHomotopy M e))

/--
概要：同じ連結成分の頂点による平行移動の像は一致する。
方針：連結成分への降下写像へ成分の等式を適用する。
規約：Segal 1974 Proposition 1.5・1.6。辺の鎖の向きを固定しない。
使われ方：群状モノイドの逆成分を代表元で扱う。
-/
theorem monoidLeftTranslation_map_eq (M : SimplicialObject MonCat.{u})
    {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
    (hL : ∀ {f g : monoidSpace M ⟶ monoidSpace M}, SSet.Homotopy f g → L.map f = L.map g)
    {a b : M.obj (op ⦋0⦌)}
    (hab : SSet.π₀.mk (X := monoidSpace M) a = SSet.π₀.mk (X := monoidSpace M) b) :
    L.map (monoidLeftTranslation M a) = L.map (monoidLeftTranslation M b) :=
  congrArg (monoidTranslationClass M L hL) hab

/--
概要：群状モノイドの頂点の平行移動はホモトピーを同一視する関手の下で可逆となる。
方針：π₀ の逆成分の頂点を選び、その平行移動が左右の逆射であることを示す。
規約：Segal 1974 Proposition 1.5・1.6。単体次数ごとの逆元は選ばない。
使われ方：bar の作用の面写像を局所化で可逆にする。
-/
noncomputable def grouplikeTranslationIso (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
    (hL : ∀ {f g : monoidSpace M ⟶ monoidSpace M}, SSet.Homotopy f g → L.map f = L.map g)
    (a : M.obj (op ⦋0⦌)) : L.obj (monoidSpace M) ≅ L.obj (monoidSpace M) := by
  letI := SimplicialMonoid.componentsMonoid M
  let u := (hG (SSet.π₀.mk (X := monoidSpace M) a)).unit
  have hu : (u : SSet.π₀ (monoidSpace M)) = SSet.π₀.mk (X := monoidSpace M) a := (hG _).unit_spec
  let b : M.obj (op ⦋0⦌) := Classical.choose (SSet.π₀.mk_surjective (u⁻¹).val)
  have hb := Classical.choose_spec (SSet.π₀.mk_surjective (u⁻¹).val)
  have hab : SSet.π₀.mk (X := monoidSpace M) (a * b) = SSet.π₀.mk (1 : M.obj (op ⦋0⦌)) := by
    change SSet.π₀.mk (X := monoidSpace M) a * SSet.π₀.mk (X := monoidSpace M) b = 1
    rw [hb, ← hu]
    exact Units.mul_inv u
  have hba : SSet.π₀.mk (X := monoidSpace M) (b * a) = SSet.π₀.mk (1 : M.obj (op ⦋0⦌)) := by
    change SSet.π₀.mk (X := monoidSpace M) b * SSet.π₀.mk (X := monoidSpace M) a = 1
    rw [hb, ← hu]
    exact Units.inv_mul u
  exact
    { hom := L.map (monoidLeftTranslation M a)
      inv := L.map (monoidLeftTranslation M b)
      hom_inv_id := by
        rw [← L.map_comp, monoidLeftTranslation_comp,
          monoidLeftTranslation_map_eq M L hL hba, monoidLeftTranslation_one, L.map_id]
      inv_hom_id := by
        rw [← L.map_comp, monoidLeftTranslation_comp,
          monoidLeftTranslation_map_eq M L hL hab, monoidLeftTranslation_one, L.map_id] }


end SerrePositivity.KST.Comparison
