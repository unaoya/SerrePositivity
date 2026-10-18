module

public import SerrePositivity.KST.Descent.BlowupSequenceData
public import SerrePositivity.KST.Descent.IdentityCenterSquare

/-!
# 同変な立方体による不変部分の列の比較

## 概要
同変な二つの幾何正方形の間の射から、不変部分の全次数の長完全列の比較を作る。

## 方針
各頂点の引き戻しの同変性を反変関手の合成保存で示す。
自然な blowup 列の比較を有理不変部分に制限して五項補題を適用する。

## 規約
中項と例外部分では、元の群の同型でなく、不変部分の指定比較の同型を使う。
境界の可換性は自然な列の入力から導かれる。

## 使われ方
論文 定理 3.1 の実際の同変軌道正方形を、基底の恒等中心正方形と比較する。
-/

@[expose] public section

universe u v w t

open CategoryTheory Representation AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：可換な立方体の四頂点の射の同変性（論文 定理 3.1）。
方針：二つの正方形の作用と、指定された四つの射の可換式を保持する。
規約：正方形の四辺の可換式は既存の射 f が保持する。
使われ方：幾何的な立方体の引き戻しを不変部分の比較へ移す。 -/
structure EquivariantSquareMap {C : Type u} [Category.{v} C] {sq tq : Square C}
    {G : Type*} [Group G] (a : SquareAction sq G) (b : SquareAction tq G) (f : sq ⟶ tq) where
  /-- 概要：左上の同変性（論文 §3）。方針：指定可換式。
  規約：例外部分の射。使われ方：中心上の比較。 -/
  equivariant1 : ∀ g, (a.on1 g).asIso.hom ≫ f.τ₁ = f.τ₁ ≫ (b.on1 g).asIso.hom
  /-- 概要：右上の同変性（論文 §3）。方針：指定可換式。
  規約：固有な変形の射。使われ方：置換表現の比較。 -/
  equivariant2 : ∀ g, (a.on2 g).asIso.hom ≫ f.τ₂ = f.τ₂ ≫ (b.on2 g).asIso.hom
  /-- 概要：左下の同変性（論文 §3）。方針：指定可換式。
  規約：閉中心の射。使われ方：帰納仮定。 -/
  equivariant3 : ∀ g, (a.on3 g).asIso.hom ≫ f.τ₃ = f.τ₃ ≫ (b.on3 g).asIso.hom
  /-- 概要：右下の同変性（論文 §3）。方針：指定可換式。
  規約：基底への射。使われ方：降下の指定比較。 -/
  equivariant4 : ∀ g, (a.on4 g).asIso.hom ≫ f.τ₄ = f.τ₄ ≫ (b.on4 g).asIso.hom

/-- 概要：基底と中心への不変な射から恒等中心正方形への同変比較（定理 3.1）。
方針：上の二頂点の同変性を、正方形の辺の同変性から導く。
規約：比較先の四頂点には自明に作用する。
使われ方：軌道正方形から分裂正方形への指定された比較。 -/
theorem toIdentityCenterSquare_equivariant {C : Type u} [Category.{v} C]
    {sq : Square C} {G : Type*} [Group G] (a : SquareAction sq G)
    {X Z : C} (i : Z ⟶ X) (base : sq.X₄ ⟶ X) (center : sq.X₃ ⟶ Z)
    (comm : sq.f₃₄ ≫ base = center ≫ i)
    (base_invariant : ∀ g, (a.on4 g).asIso.hom ≫ base = base)
    (center_invariant : ∀ g, (a.on3 g).asIso.hom ≫ center = center) :
    EquivariantSquareMap a (SquareAction.trivial (identityCenterSquare i) G)
      (toIdentityCenterSquare sq i base center comm) where
  equivariant1 g := by
    change (a.on1 g).asIso.hom ≫ (sq.f₁₃ ≫ center) = (sq.f₁₃ ≫ center) ≫ 𝟙 Z
    rw [Category.comp_id, ← Category.assoc, a.equivariant13 g, Category.assoc,
      center_invariant g]
  equivariant2 g := by
    change (a.on2 g).asIso.hom ≫ (sq.f₂₄ ≫ base) = (sq.f₂₄ ≫ base) ≫ 𝟙 X
    rw [Category.comp_id, ← Category.assoc, a.equivariant24 g, Category.assoc, base_invariant g]
  equivariant3 g := by
    change (a.on3 g).asIso.hom ≫ center = center ≫ 𝟙 Z
    simpa only [Category.comp_id] using center_invariant g
  equivariant4 g := by
    change (a.on4 g).asIso.hom ≫ base = base ≫ 𝟙 X
    simpa only [Category.comp_id] using base_invariant g

/-- 概要：同変な幾何射の引き戻しは前層の左表現の同変写像（論文 (3.7)）。
方針：逆元の引き戻しと、前層の合成保存の可換式を使う。
規約：群の有限性は不要。
使われ方：幾何的な立方体の四つの比較の同変性。 -/
theorem GradedPresheaf.pullback_isIntertwiningMap
    {C : Type u} [Category.{v} C] {Coefficient : Type w}
    (L : GradedPresheaf.{u, v, w, t} C Coefficient) (H : Coefficient) (n : ℤ)
    {X Y : C} (f : X ⟶ Y) {G : Type*} [Group G]
    (actionX : G →* Aut X) (actionY : G →* Aut Y)
    (equivariant : ∀ g, (actionX g).asIso.hom ≫ f = f ≫ (actionY g).asIso.hom) :
    IsIntertwiningMap (L.pullbackRepresentation H n actionY)
      (L.pullbackRepresentation H n actionX) (L.pullback H n f) := by
  constructor
  intro g x
  exact (LinearMap.congr_fun (L.pullback_action_comm H n f actionX actionY equivariant g⁻¹) x).symm

namespace NaturalBlowupSequences

variable {S : Scheme.{u}} {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
variable (data : NaturalBlowupSequences L) (s t : AbstractBlowupSquare S)
variable {G : Type*} [Group G] (a : SquareAction s.square G) (b : SquareAction t.square G)
variable (f : s.square ⟶ t.square) (e : EquivariantSquareMap a b f) (H : Coefficient)

include e

/-- 概要：同変な立方体から自然な blowup 列の同変比較（論文 定理 3.1）。
方針：四頂点の引き戻しの同変性と境界の自然性を組み合わせる。
規約：比較の各成分は指定された幾何射の引き戻し。
使われ方：比較を有理不変部分の全次数の完全列へ制限する。 -/
theorem equivariantComparison :
    GradedMayerVietoris.EquivariantHom (data.comparison s t f H)
      (data.action t H b) (data.action s H a) where
  mapA_equivariant n := L.pullback_isIntertwiningMap H n f.τ₄ a.on4 b.on4 e.equivariant4
  mapB_equivariant n := by
    constructor
    intro g x
    apply Prod.ext
    · exact (L.pullback_isIntertwiningMap H n f.τ₂ a.on2 b.on2 e.equivariant2).isIntertwining g x.1
    · exact (L.pullback_isIntertwiningMap H n f.τ₃ a.on3 b.on3 e.equivariant3).isIntertwining g x.2
  mapC_equivariant n := L.pullback_isIntertwiningMap H n f.τ₁ a.on1 b.on1 e.equivariant1

/-- 概要：同変な立方体による不変部分の全次数の列の比較（論文 定理 3.1）。
方針：自然な同変比較を有限群の有理不変部分へ制限する。
規約：境界も含む列の射。
使われ方：軌道正方形と基底の恒等中心正方形の五項補題。 -/
noncomputable def fixedComparison [Finite G] :
    GradedMayerVietoris.Hom (data.fixedSequence t H b) (data.fixedSequence s H a) :=
  (data.equivariantComparison s t a b f e H).fixedHom

/-- 概要：二つの既知の不変部分の比較から基底の指定比較の全単射性（定理 3.1）。
方針：自然な境界を含む固定部分の列の射へ全次数の五項補題を適用する。
規約：任意の係数 H を固定し、すべての整数次数を同時に仮定する。
使われ方：(3.8) と中心上の帰納を実際の幾何比較へ接続する。 -/
theorem fixedComparison_bijective_base [Finite G]
    (product_comparison : ∀ n, Function.Bijective ((data.fixedComparison s t a b f e H).mapB n))
    (exceptional_comparison : ∀ n,
      Function.Bijective ((data.fixedComparison s t a b f e H).mapC n)) (n : ℤ) :
    Function.Bijective ((data.fixedComparison s t a b f e H).mapA n) :=
  (data.fixedComparison s t a b f e H).bijective_mapA product_comparison exceptional_comparison n

end NaturalBlowupSequences

end SerrePositivity.KST.Descent
