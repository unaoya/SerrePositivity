module
public import SerrePositivity.KST.SConstruction.CoherentOrdinaryPrism
public import SerrePositivity.KST.SConstruction.KOriginalSuspensionPrisms

/-! # 元の K prism から直接作る全合成列の native Hom 族
概要：元の K prism を通常積圏の nerve 上に厳密に表示し、その全合成列を native Hom へ評価する。
方針：同じ prism の始域同型に前合成し、全合成列の実評価と収縮をそのまま適用する。
規約：全段・全高次入力を保持し、円柱族の存在や標的の局所 Kan 性を追加仮定にしない。
使われ方：元の長辺から二つの元の合成への全パラメータの円柱を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismNativeStringFamilies_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の全入力 K prism を、同じ通常積圏の nerve 上に厳密に表示する。 -/
def kKanOriginalPrismStringDiagram {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶
      SimplicialNerve PointedSimplicialSet.{u} :=
  (coherentOrdinaryPrismIso.{u, u + 1} I).hom ≫ (kKanOriginalSuspensionHomotopy F r).h

/-- 始域を元に戻すと、元の全入力 K prism の実円柱そのものを回収する。 -/
lemma kKanOriginalPrismStringDiagram_recover {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (coherentOrdinaryPrismIso.{u, u + 1} I).inv ≫ kKanOriginalPrismStringDiagram r F =
      (kKanOriginalSuspensionHomotopy F r).h := by
  rw [kKanOriginalPrismStringDiagram, Iso.inv_hom_id_assoc]

/-- 全単体に制限しても、元の K の同じ prism を全次数で厳密に回収する。 -/
lemma kKanOriginalPrismStringDiagram_simplex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    (SSet.yonedaEquiv.symm (ULift.up s) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentOrdinaryPrismIso.{u, u + 1} I).inv ≫ kKanOriginalPrismStringDiagram r F =
        kKanOriginalSuspensionPrism r F s := by
  rw [kKanOriginalPrismStringDiagram_recover]
  rfl

/-- 元の K prism の任意の射の全合成列を、同じ両端の native Hom の実族へ束ねる。 -/
def kKanOriginalPrismNativeFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {a b : I × ULift.{u} (Fin 2)} (f : a ⟶ b) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶
      SimplicialCategory.sHom (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) a)
        (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) b) :=
  coherentArrowNativeFamily (kKanOriginalPrismStringDiagram r F) f

/-- 元の K prism の長辺の値から全合成列の native 評価へ向かう実円柱。 -/
def kKanOriginalPrismNativeContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {a b : I × ULift.{u} (Fin 2)} (f : a ⟶ b) :
    SSet.Homotopy
      (SSet.const (coherentArrowNativeInitialVertex (kKanOriginalPrismStringDiagram r F) f))
      (kKanOriginalPrismNativeFamily r F f) :=
  coherentArrowNativeContraction (kKanOriginalPrismStringDiagram r F) f

end SerrePositivity.KST.SConstruction
