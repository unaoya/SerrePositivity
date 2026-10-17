module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Functor.HomotopyAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveCriterion

/-! # graph延長の主K随伴とホモトピー射影性の保存

## 概要
graph延長の主K随伴とホモトピー射影性の保存。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 制限の全Homモデルを使った、既存の閉零随伴。 -/
def dgModuleEnrichedRestrictionAdjunction :
    (dgModuleExtension A D E F).onClosed ⊣ (dgModuleRestriction A D E F.op).onClosed :=
  (dgModuleExtensionRestrictionAdjunction A D E F).ofNatIsoRight
    (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm

/-- 主ホモトピー圏上でのgraph延長–制限随伴。 -/
def dgModuleHomotopyAdjunction :
    (dgModuleExtension A D E F).onHomotopy ⊣ (dgModuleRestriction A D E F.op).onHomotopy :=
  DGFunctor.homotopyAdjunction _ _ (dgModuleEnrichedRestrictionAdjunction A D E F)

lemma dgModuleHomotopyRestriction_quasiIso
    {M N : ModuleHomotopyCategory A E} (f : M ⟶ N)
    (hf : moduleHomotopyQuasiIso A E f) :
    moduleHomotopyQuasiIso A D ((dgModuleRestriction A D E F.op).onHomotopy.map f) := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A E).map_surjective f
  change moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map
    ((dgModuleRestriction A D E F.op).onClosed.map g))
  rw [dgModuleRestriction_map]
  exact (moduleHomotopyQuasiIso_map_iff A D _).mpr
    (moduleRestriction_quasiIso A D E F.op g ((moduleHomotopyQuasiIso_map_iff A E g).mp hf))

/-- 任意のdg関手のgraph延長はホモトピー射影的右加群を保つ。 -/
lemma dgModuleExtension_homotopicallyProjective {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) :
    moduleHomotopicallyProjective A E ((dgModuleExtension A D E F).onClosed.obj P) := by
  apply moduleHomotopicallyProjective_of_coyoneda_inverts A E
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  let adj := dgModuleHomotopyAdjunction A D E F
  let Rf := (dgModuleRestriction A D E F.op).onHomotopy.map f
  have hRf := dgModuleHomotopyRestriction_quasiIso A D E F f hf
  have hpost := (CategoryTheory.isIso_iff_bijective _).mp
    (moduleHomotopicallyProjective_coyoneda_inverts A D hP Rf hRf)
  change Function.Bijective (fun s :
    (dgModuleExtension A D E F).onHomotopy.obj ((moduleToHomotopy A D).obj P) ⟶ X => s ≫ f)
  let eX := adj.homEquiv ((moduleToHomotopy A D).obj P) X
  let eY := adj.homEquiv ((moduleToHomotopy A D).obj P) Y
  have heq : (fun s :
      (dgModuleExtension A D E F).onHomotopy.obj ((moduleToHomotopy A D).obj P) ⟶ X => s ≫ f) =
    fun s => eY.symm (eX s ≫ Rf) := by
    funext s
    apply eY.injective
    rw [Equiv.apply_symm_apply]
    exact adj.homEquiv_naturality_right s f
  rw [heq]
  exact eY.symm.bijective.comp (hpost.comp eX.bijective)

end SerrePositivity.DifferentialGraded
