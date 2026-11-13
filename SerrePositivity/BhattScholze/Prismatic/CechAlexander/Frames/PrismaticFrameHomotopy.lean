module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.CechVertexHomotopy
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra.FrameHelpers
import all SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.CechVertexHomotopy

/-!
# prismatic 枠の余鎖ホモトピー

## 概要
同じ剰余構造射を持つ二つの枠の射を、混合頂点で結ぶ。

## 方針
各次数で変数像を指定して、prismatic 包からの射の存在と一意性を適用する。
余単体恒等式は頂点だけの共通補題に渡し、台加群の交代余面複体へ移す。

## 規約
各対象は同じ基底 prism と同じ剰余環の上に置く。

## 使われ方
BS 著者版 Remark 4.19 の有限枠と大きい枠の表示独立性。
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u})

/-- 余単体的な prismatic 枠の変数とその延長の普遍性。 -/
structure PrismOverVertexFrame (X : CosimplicialObject (PrismOver P R κ)) (S : Type v) where
  /-- 変数の剰余での評価。 -/
  residue : S → R
  /-- 各頂点の変数像。 -/
  variableImage : ∀ n : ℕ, S → Fin (n + 1) → (X.obj ⦋n⦌).B
  /-- 変数像と剰余の評価との照合。 -/
  variable_mod : ∀ n x i,
    Ideal.Quotient.mk (X.obj ⦋n⦌).Q.ideal (variableImage n x i) = (X.obj ⦋n⦌).sec (residue x)
  /-- 単体の射は頂点を写す。 -/
  variable_map : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) x i,
    (X.map θ).toHom.toRingHom (variableImage m x i) = variableImage n x (θ.toOrderHom i)
  /-- 剰余と両立する像を指定すれば射が一意に得られる。 -/
  lift : ∀ (n : ℕ) (Y : PrismOver P R κ) (z : S → Fin (n + 1) → Y.B),
    (∀ x i, Ideal.Quotient.mk Y.Q.ideal (z x i) = Y.sec (residue x)) →
    ∃! f : X.obj ⦋n⦌ ⟶ Y, ∀ x i, f.toHom.toRingHom (variableImage n x i) = z x i

namespace PrismOverVertexFrame

variable {P R κ} {X Y : CosimplicialObject (PrismOver P R κ)} {S : Type v}
variable (D : PrismOverVertexFrame P R κ X S)

private theorem map_variable_mod {n : ℕ} {T : PrismOver P R κ}
    (f : X.obj ⦋n⦌ ⟶ T) (x : S) (i : Fin (n + 1)) :
    Ideal.Quotient.mk T.Q.ideal (f.toHom.toRingHom (D.variableImage n x i)) =
      T.sec (D.residue x) := by
  rw [← OrientedPrism.Hom.quotientMap_mk, D.variable_mod]
  exact RingHom.congr_fun f.comm_sec (D.residue x)

/-- 枠の射は変数で決まる。 -/
theorem hom_ext {n : ℕ} {T : PrismOver P R κ} {f g : X.obj ⦋n⦌ ⟶ T}
    (h : ∀ x i, f.toHom.toRingHom (D.variableImage n x i) =
      g.toHom.toRingHom (D.variableImage n x i)) : f = g := by
  have hU := D.lift n T (fun x i => g.toHom.toRingHom (D.variableImage n x i))
    (map_variable_mod D g)
  exact hU.unique h (fun _ _ => rfl)

private def underlying (P : OrientedPrism p A) (R : Type u) [CommRing R]
    [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u}) : PrismOver P R κ ⥤ Type u :=
  { obj T := T.B
    map f := TypeCat.ofHom f.toHom.toRingHom
    map_id _ := rfl
    map_comp _ _ := rfl }

variable (f g : X ⟶ Y)

private theorem mixedAt_mod {n : ℕ} (j : Fin (n + 1)) (x : S) (i : Fin (n + 2)) :
    Ideal.Quotient.mk (Y.obj ⦋n⦌).Q.ideal
      (CechVertexHomotopy.mixedValue (underlying P R κ) f g D.variableImage j x i) =
        (Y.obj ⦋n⦌).sec (D.residue x) := by
  unfold CechVertexHomotopy.mixedValue CechVertexHomotopy.atVertex
  let v := Y.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (j.predAbove i))
  change Ideal.Quotient.mk (Y.obj ⦋n⦌).Q.ideal
    (v.toHom.toRingHom (if i ≤ j.castSucc then
      (f.app ⦋0⦌).toHom.toRingHom (D.variableImage 0 x 0)
      else (g.app ⦋0⦌).toHom.toRingHom (D.variableImage 0 x 0))) = _
  rw [← OrientedPrism.Hom.quotientMap_mk]
  split_ifs
  · rw [map_variable_mod D (f.app ⦋0⦌)]
    exact RingHom.congr_fun v.comm_sec (D.residue x)
  · rw [map_variable_mod D (g.app ⦋0⦌)]
    exact RingHom.congr_fun v.comm_sec (D.residue x)

private def mixedAt {n : ℕ} (j : Fin (n + 1)) :
    X.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌ :=
  (D.lift (n + 1) (Y.obj ⦋n⦌) _ (mixedAt_mod D f g j)).choose

private theorem mixedAt_variable {n : ℕ} (j : Fin (n + 1)) (x : S) (i : Fin (n + 2)) :
    (underlying P R κ).map (mixedAt D f g j) (D.variableImage (n + 1) x i) =
      CechVertexHomotopy.mixedValue (underlying P R κ) f g D.variableImage j x i :=
  (D.lift (n + 1) (Y.obj ⦋n⦌) _ (mixedAt_mod D f g j)).choose_spec.1 x i

/-- 二つの枠の射の余単体ホモトピー。 -/
def simplicialHomotopy :
    SimplicialObject.Homotopy
      ((cosimplicialSimplicialEquiv _).functor.map f.op)
      ((cosimplicialSimplicialEquiv _).functor.map g.op) :=
  CechVertexHomotopy.ofMixedVertices (underlying P R κ) f g D.variableImage
    (fun θ x i => D.variable_map θ x i)
    (fun h => D.hom_ext h)
    (fun j => mixedAt D f g j)
    (fun j x i => mixedAt_variable D f g j x i)

/-- 台加群の交代余面複体上の余鎖ホモトピー。 -/
def cochainHomotopy :
    let G := prismSiteAlgebras P R κ ⋙ PDCechNerve.algebraModule A
    Homotopy ((alternatingCofaceMapComplex _).map (Functor.whiskerRight f G))
      ((alternatingCofaceMapComplex _).map (Functor.whiskerRight g G)) :=
  Cosimplicial.CosimplicialHomotopy.toCochainHomotopy
    ((simplicialHomotopy D f g).whiskerRight
      (prismSiteAlgebras P R κ ⋙ PDCechNerve.algebraModule A).op)

end PrismOverVertexFrame
end SerrePositivity.BhattScholze.Prismatic
