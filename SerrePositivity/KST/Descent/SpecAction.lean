module

public import SerrePositivity.KST.Descent.GeometricFiberTransitivity

/-!
# 環の作用が定める Spec 上の作用

## 概要
環の左作用から Spec 上の左作用を構成し、幾何的推移性との対応を証明する。

## 方針
Spec は反変なので群元の逆元を使う。群の法則は環準同型の等式で検査する。

## 規約
既存の幾何ファイバーの定義は g の comap を使うため、推移性を移す際も逆元を取る。

## 使われ方
論文 定理 3.1 の移動切断と、基底上の実際のスキームの群作用。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {T G : Type u} [CommRing T] [Group G] [MulSemiringAction G T]

/-- 概要：環の作用から Spec の自己同型を構成（論文 定理 3.1）。
方針：逆元による環準同型を hom とし、元による環準同型を inv とする。
規約：Spec の反変性を逆元で補う。
使われ方：Spec 上の左群作用の各自己同型。 -/
noncomputable def specActionIso (g : G) : Spec (.of T) ≅ Spec (.of T) where
  hom := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T g⁻¹))
  inv := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T g))
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact inv_smul_smul g x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact smul_inv_smul g x

/-- 概要：環の作用から Spec 上の左群作用（論文 定理 3.1）。
方針：構成した自己同型の積の法則を Spec の忠実性で証明する。
規約：hom は g⁻¹ の comap である。
使われ方：有限型の圏内へ持ち上げる実際の幾何的作用。 -/
noncomputable def specAction : G →* Aut (Spec (.of T)) where
  toFun g := Aut.of (specActionIso g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T (1 : G)⁻¹)) = 𝟙 _
    rw [← Spec.map_id]
    congr 1
    ext x
    change (1 : G)⁻¹ • x = x
    simp
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T (g * h)⁻¹)) =
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T h⁻¹)) ≫
        Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T g⁻¹))
    rw [← Spec.map_comp]
    congr 1
    ext x
    change (g * h)⁻¹ • x = h⁻¹ • g⁻¹ • x
    rw [mul_inv_rev, mul_smul]

variable {A : Type u} [CommRing A] [Algebra A T] [SMulCommClass G A T]

/-- 概要：A 線形な環の作用は Spec A 上の作用（論文 定理 3.1）。
方針：代数射が algebraMap を保存する等式へ反変に Spec を適用する。
規約：スキームの射として基底上の等式を証明する。
使われ方：作用を有限型の圏内の作用へ移す条件。 -/
theorem specAction_over_base (g : G) :
    (specAction (T := T) g).asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A T)) =
      Spec.map (CommRingCat.ofHom (algebraMap A T)) := by
  change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T g⁻¹)) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (MulSemiringAction.toAlgHom A T g⁻¹).commutes a

/-- 概要：既存の幾何的推移性は実際の Spec 作用の点の推移性を与える（定理 3.1）。
方針：通常のファイバー上の推移性で得る群元の逆元を選ぶ。
規約：定義上の comap と Spec の左作用の向きの差を明示的に処理する。
使われ方：移動切断の像の被覆条件の幾何的入力。 -/
theorem specAction_transitive_on_fibers (transitive : IsGeometricallyTransitive A T G)
    (x y : Spec (.of T))
    (same_base : Spec.map (CommRingCat.ofHom (algebraMap A T)) x =
      Spec.map (CommRingCat.ofHom (algebraMap A T)) y) :
    ∃ g : G, (specAction (T := T) g).asIso.hom x = y := by
  obtain ⟨g, hg⟩ := geometricTransitivity_on_fibers transitive x y same_base
  refine ⟨g⁻¹, ?_⟩
  change PrimeSpectrum.comap (MulSemiringAction.toRingHom G T (g⁻¹)⁻¹) x = y
  simpa only [inv_inv] using hg

end SerrePositivity.KST.Descent
