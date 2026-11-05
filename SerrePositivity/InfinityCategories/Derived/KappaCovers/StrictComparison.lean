module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.NativeRetract
public import SerrePositivity.InfinityCategories.Derived.NerveInclusion
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve

/-!
概要：通常の実加群図式を固定したまま、D-bar の native/strict 比較の消費型を記述する。
方針：閉零圏の nerve 包含と正本の実分解関手を合成する。
規約：この比較の存在は証明せず明示引数に保持する。使われ方：D-8 d の native 表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の閉零圏の対象に、同じ dg Hom を保つ閉零ラベルを一つ付ける。 -/
def dgKappaModuleClosedRelabel : ModuleCategory R D ⥤ ClosedCategory R (ModuleCategory R D) where
  obj M := ForgetEnrichment.of (Complex R) M
  map f := ForgetEnrichment.homOf (Complex R) (ForgetEnrichment.homTo (Complex R) f)

/-- 同じ通常の図式を全単体上で正本の実導来 ∞ 圏へ送る。 -/
def dgKappaStrictModuleDiagram {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D) :
    (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      dgModuleDerivedInfinityCategory R D :=
  (show (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      nerve (ClosedCategory R (ModuleCategory R D)) from {
    app _ := ↾fun s => (s.down ⋙ F) ⋙ dgKappaModuleClosedRelabel R D }) ≫
    closedNerveInclusion R (ModuleCategory R D) ≫ dgConeModuleDerived R D

lemma dgKappaStrictModuleDiagram_vertex {J : Type u} [Category J]
    (F : J ⥤ ModuleCategory R D) (i : (nerve J) _⦋0⦌) :
    (dgKappaStrictModuleDiagram R D F).app (Opposite.op ⦋0⦌) (ULift.up i) =
      dgConeModuleDerivedVertex R D (F.obj (i.obj 0)) := by
  change (dgConeModuleDerived R D).app _
    ((closedNerveInclusion R (ModuleCategory R D)).app _
      ((i ⋙ F) ⋙ dgKappaModuleClosedRelabel R D)) = _
  apply congrArg ((dgConeModuleDerived R D).app _)
  apply (dgNerve.vertexEquiv R (ModuleCategory R D)).injective
  rw [closedNerveInclusion_vertex]
  rfl

/-- D-bar に要求する最小の結論：固定した同じ strict 図式の native 余極限と頂点比較。
この命題自体の証明を追加したものではない。 -/
def DGKappaStrictFilteredColimitComparison (κ : Cardinal.{u}) [Fact κ.IsRegular] : Prop :=
  ∀ (J : Type u) [PartialOrder J] [IsCardinalFiltered J κ]
    (F : J ⥤ ModuleCategory R D) (c : Cocone F), IsColimit c →
    ∃ t : JoinCocone (dgKappaStrictModuleDiagram R D F), IsColimitCone t ∧
      Nonempty (VertexIso t.vertex (dgConeModuleDerivedVertex R D c.pt))

end SerrePositivity.InfinityCategories
