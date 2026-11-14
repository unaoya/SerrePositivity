module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：任意の環の係数図式で Frobenius 順極限を取り、環の射に自然な整数加群の図式を作る。
方針：各対象・射で実際の環の順極限を取り、有限段の元で関手律と自然性を示す。
規約：標数条件は p が零になることで与え、零環・空の標準開を除外しない。
使われ方：F8 の共通細分・底変換・閉厚化の実際の環の射と Frobenius の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v w
variable {J : Type w} [Category.{v} J]
variable (D : J ⥤ CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hD : ∀ T, (p : D.obj T) = 0)

/-- 各対象の実際の環の Frobenius 順極限を係数とする図式。 -/
def frobeniusRingDiagram : J ⥤ ModuleCat.{u} ℤ where
  obj T := ModuleCat.of ℤ (FrobeniusDirectLimit (D.obj T) p hp (hD T))
  map {T U} f := ModuleCat.ofHom
    (frobeniusDirectLimitMap p hp (hD T) (hD U) (D.map f).hom).toAddMonoidHom.toIntLinearMap
  map_id T := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (D.obj T) p hp (hD T)) x
    change frobeniusDirectLimitOf (D.obj T) p hp (hD T) n ((D.map (𝟙 T)).hom x) =
      frobeniusDirectLimitOf (D.obj T) p hp (hD T) n x
    rw [D.map_id]
    rfl
  map_comp {T U V} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (D.obj T) p hp (hD T)) x
    change frobeniusDirectLimitOf (D.obj V) p hp (hD V) n ((D.map (f ≫ g)).hom x) =
      frobeniusDirectLimitOf (D.obj V) p hp (hD V) n ((D.map g).hom ((D.map f).hom x))
    rw [D.map_comp]
    rfl

variable {D} {E F : J ⥤ CommRingCat.{u}}
variable {hE : ∀ T, (p : E.obj T) = 0} {hF : ∀ T, (p : F.obj T) = 0}

/-- 実際の環の図式の射が誘導する Frobenius 順極限の自然変換。 -/
def frobeniusRingDiagramMap (η : D ⟶ E) :
    frobeniusRingDiagram D p hp hD ⟶ frobeniusRingDiagram E p hp hE where
  app T := ModuleCat.ofHom
    (frobeniusDirectLimitMap p hp (hD T) (hE T) (η.app T).hom).toAddMonoidHom.toIntLinearMap
  naturality {T U} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (D.obj T) p hp (hD T)) x
    change frobeniusDirectLimitOf (E.obj U) p hp (hE U) n ((η.app U).hom ((D.map f).hom x)) =
      frobeniusDirectLimitOf (E.obj U) p hp (hE U) n ((E.map f).hom ((η.app T).hom x))
    exact congrArg (frobeniusDirectLimitOf (E.obj U) p hp (hE U) n)
      (congrArg (fun m ↦ m.hom x) (η.naturality f))

/-- 係数図式の恒等射を保つ。 -/
theorem frobeniusRingDiagramMap_id :
    frobeniusRingDiagramMap p hp hD (hE := hD) (𝟙 D) = 𝟙 _ := by
  ext T x
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (D.obj T) p hp (hD T)) x
  rfl

/-- 係数図式の射の合成を保つ。 -/
theorem frobeniusRingDiagramMap_comp (η : D ⟶ E) (θ : E ⟶ F) :
    frobeniusRingDiagramMap p hp hD (hE := hF) (η ≫ θ) =
      frobeniusRingDiagramMap p hp hD (hE := hE) η ≫
        frobeniusRingDiagramMap p hp hE (hE := hF) θ := by
  ext T x
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (D.obj T) p hp (hD T)) x
  rfl

/-- 係数図式の同型は、実際の Frobenius 順極限の係数図式の同型を与える。 -/
def frobeniusRingDiagramIso (e : D ≅ E) :
    frobeniusRingDiagram D p hp hD ≅ frobeniusRingDiagram E p hp hE where
  hom := frobeniusRingDiagramMap p hp hD e.hom
  inv := frobeniusRingDiagramMap p hp hE e.inv
  hom_inv_id := by
    rw [← frobeniusRingDiagramMap_comp, e.hom_inv_id, frobeniusRingDiagramMap_id]
  inv_hom_id := by
    rw [← frobeniusRingDiagramMap_comp, e.inv_hom_id, frobeniusRingDiagramMap_id]

/-- 添字の引き戻しと、実際の環ごとの Frobenius 順極限は同じ図式を与える。 -/
theorem frobeniusRingDiagram_precomp {K : Type*} [Category K] (F : K ⥤ J) :
    frobeniusRingDiagram (F ⋙ D) p hp (fun T ↦ hD (F.obj T)) =
      F ⋙ frobeniusRingDiagram D p hp hD := rfl

/-- 環の図式の射も、添字の引き戻しと Frobenius 順極限の交換に整合する。 -/
theorem frobeniusRingDiagramMap_precomp {K : Type*} [Category K]
    (F : K ⥤ J) (η : D ⟶ E) :
    frobeniusRingDiagramMap p hp (fun T ↦ hD (F.obj T))
      (hE := fun T ↦ hE (F.obj T)) (Functor.whiskerLeft F η) =
      Functor.whiskerLeft F (frobeniusRingDiagramMap p hp hD (hE := hE) η) := rfl

/-- 実際の環の切断の可換四角は、Frobenius 順極限後も同じ可換四角を与える。 -/
theorem frobeniusRingDiagramMap_commutes {G : J ⥤ CommRingCat.{u}}
    (hG : ∀ T, (p : G.obj T) = 0)
    (η : D ⟶ E) (θ : F ⟶ G) (α : D ⟶ F) (β : E ⟶ G)
    (h : η ≫ β = α ≫ θ) :
    frobeniusRingDiagramMap p hp hD (hE := hE) η ≫
        frobeniusRingDiagramMap p hp hE (hE := hG) β =
      frobeniusRingDiagramMap p hp hD (hE := hF) α ≫
        frobeniusRingDiagramMap p hp hF (hE := hG) θ := by
  rw [← frobeniusRingDiagramMap_comp, ← frobeniusRingDiagramMap_comp, h]

end SerrePositivity.AlgebraicGeometry
