module

public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.CategoryTheory.CechNerveData

/-!
# 変数の普遍性からの Čech–Alexander 対象の組み立て

## 概要
剰余環の各元と頂点で添字づけた変数の普遍性を、site の対象として扱う。

## 方針
変数像の指定による一意な射を入力し、余単体的構造・弱始性・余積を構成する。

## 規約
BS 著者版 Construction 4.17–4.18。包絡の選択から得られる計算用のデータ。

## 使われ方
一般の HasEnvelopes と既存の BigCechTerm に共通する組み立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 概要：変数の像で射が一意に決まる Čech–Alexander の一項のデータ。
方針：実際の site の対象と変数、剰余条件を満たす持ち上げの普遍性を持つ。
規約：BS 著者版 Construction 4.17。包絡の定義を置き換えるものではない。
使われ方：包絡の普遍性から余積と単体射を組み立てる。 -/
structure CechAlexanderPresentation (n : ℕ) where
  X : PrismOver P R κ
  coordinate : R × Fin (n + 1) → X.B
  coordinate_mod : ∀ s, Ideal.Quotient.mk X.Q.ideal (coordinate s) = X.sec s.1
  liftVariables : ∀ (D : PrismOver P R κ) (v : R × Fin (n + 1) → D.B),
    (∀ s, Ideal.Quotient.mk D.Q.ideal (v s) = D.sec s.1) →
      ∃! f : X ⟶ D, ∀ s, f.toHom.toRingHom (coordinate s) = v s

namespace CechAlexanderPresentation
variable {m n l : ℕ} (E : CechAlexanderPresentation (P := P) (R := R) (κ := κ) m)

/-- 概要：site の射が変数を送る像は剰余の構造射と両立する。
方針：剰余の射との可換性を変数で評価する。
規約：BS 著者版 Construction 4.17。使われ方：普遍性による射の一意性。 -/
theorem hom_variable_mod {D : PrismOver P R κ} (f : E.X ⟶ D) (s : R × Fin (m + 1)) :
    Ideal.Quotient.mk D.Q.ideal (f.toHom.toRingHom (E.coordinate s)) = D.sec s.1 := by
  rw [← OrientedPrism.Hom.quotientMap_mk, E.coordinate_mod]
  exact RingHom.congr_fun f.comm_sec s.1

/-- 概要：変数上で一致する site の二射は等しい。
方針：変数像の持ち上げの一意性を使う。
規約：BS 著者版 Construction 4.17。使われ方：関手性と余積の一意性。 -/
theorem hom_ext {D : PrismOver P R κ} {f g : E.X ⟶ D}
    (h : ∀ s, f.toHom.toRingHom (E.coordinate s) = g.toHom.toRingHom (E.coordinate s)) : f = g := by
  obtain ⟨a, _, ha⟩ := E.liftVariables D (fun s => g.toHom.toRingHom (E.coordinate s))
    (E.hom_variable_mod g)
  exact (ha f h).trans (ha g (fun _ => rfl)).symm

variable (F : CechAlexanderPresentation (P := P) (R := R) (κ := κ) n)

/-- 頂点の写像による site の射。BS 著者版 Construction 4.18。 -/
def map (θ : Fin (m + 1) → Fin (n + 1)) : E.X ⟶ F.X :=
  (E.liftVariables F.X (fun s => F.coordinate (s.1, θ s.2))
    (fun s => F.coordinate_mod (s.1, θ s.2))).choose

/-- 頂点の写像は指定した変数をその頂点へ送る。 -/
theorem map_variable (θ : Fin (m + 1) → Fin (n + 1)) (s : R × Fin (m + 1)) :
    (E.map F θ).toHom.toRingHom (E.coordinate s) = F.coordinate (s.1, θ s.2) :=
  (E.liftVariables F.X (fun s => F.coordinate (s.1, θ s.2))
    (fun s => F.coordinate_mod (s.1, θ s.2))).choose_spec.1 s

/-- 恒等な頂点写像による射は恒等射。 -/
theorem map_id : E.map E id = 𝟙 E.X := by
  apply E.hom_ext
  intro s
  exact E.map_variable E id s

/-- 頂点写像の合成は site の射の合成と両立する。 -/
theorem map_comp (G : CechAlexanderPresentation (P := P) (R := R) (κ := κ) l)
    (θ : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → Fin (l + 1)) :
    E.map F θ ≫ F.map G τ = E.map G (τ ∘ θ) := by
  apply E.hom_ext
  intro s
  change (F.map G τ).toHom.toRingHom ((E.map F θ).toHom.toRingHom (E.coordinate s)) = _
  rw [E.map_variable, F.map_variable, E.map_variable]
  rfl

/-- 概要：各項の変数の普遍性から余単体的な site の対象を作る。
方針：単体射を頂点の写像として持ち上げる。
規約：BS 著者版 Construction 4.18。使われ方：Čech 余脈体と交代余面複体。 -/
def cosimplicial (E : ∀ n, CechAlexanderPresentation (P := P) (R := R) (κ := κ) n) :
    CosimplicialObject (PrismOver P R κ) where
  obj n := (E n.len).X
  map θ := (E _).map (E _) θ.toOrderHom
  map_id n := (E n.len).map_id
  map_comp θ τ := ((E _).map_comp (E _) (E _) θ.toOrderHom τ.toOrderHom).symm

/-- 概要：各項は環の向きで弱始対象。
方針：標的の剰余への全射で全変数を持ち上げる。
規約：BS 著者版 Construction 4.17。使われ方：特に零次の弱始性。 -/
theorem weaklyInitial : CategoryTheory.IsWeaklyInitial E.X := by
  intro D
  let v (s : R × Fin (m + 1)) : D.B :=
    (Ideal.Quotient.mk_surjective (D.sec s.1)).choose
  have hv (s : R × Fin (m + 1)) : Ideal.Quotient.mk D.Q.ideal (v s) = D.sec s.1 :=
    (Ideal.Quotient.mk_surjective (D.sec s.1)).choose_spec
  exact ⟨(E.liftVariables D v hv).choose⟩

end CechAlexanderPresentation
end SerrePositivity.BhattScholze.Prismatic
