module
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanCoefficientFibration
public import SerrePositivity.InfinityCategories.Core.ContractibleKan

/-! # 可縮な選択空間の図式の coherent な全選択
概要：成分が可縮 Kan な小図式の Bousfield–Kan end は可縮 Kan。
方針：一点への成分ごとの自明 fibration と、その end 上の持ち上げ性を使う。
規約：遷移の fibration 性も厳密な切断の存在も仮定しない。
使われ方：全入力射列の自然性パラメーターを compatible に選び、既存境界を保って延ばす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial

/-- 全ての係数を選択された終対象にした図式。 -/
def selectionTerminalDiagram (I : Type u) [SmallCategory I] : I ⥤ SSet.{u} :=
  (Functor.const I).obj (⊤_ SSet.{u})

/-- 各選択空間から一点へ忘れる自然変換。 -/
def selectionTerminalMap {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) :
    F ⟶ selectionTerminalDiagram I where
  app i := terminal.from (F.obj i)
  naturality _ _ _ := terminal.hom_ext _ _

/-- 終対象を係数とする重み付き切断空間自体も終対象。 -/
def selectionTerminalSections_isTerminal {I : Type u} [SmallCategory I]
    (W : I ⥤ SSet.{u}) : IsTerminal (weightedSections W (selectionTerminalDiagram I)) := by
  let s (A : SSet.{u}) : W ⊗ (Functor.const I).obj A ⟶ selectionTerminalDiagram I := {
    app i := terminal.from _
    naturality _ _ _ := terminal.hom_ext _ _ }
  refine IsTerminal.ofUniqueHom (fun A => weightedSectionsLift (s A)) ?_
  intro A f
  apply (weightedSectionsHomEquiv W (selectionTerminalDiagram I) A).injective
  apply NatTrans.ext
  funext i
  exact terminal.hom_ext _ _

/-- 可縮な全係数の Bousfield–Kan end は、全境界を充填できる可縮 Kan 空間。 -/
lemma contractibleDiagramSelections_isContractibleKan {I : Type u} [SmallCategory I]
    (F : I ⥤ SSet.{u}) (hF : ∀ i, IsContractibleKan (F.obj i)) :
    IsContractibleKan (bousfieldKanHolim F) := by
  let t := selectionTerminalMap F
  have ht (i : I) : TrivialKanFibration (t.app i) :=
    (isContractibleKan_iff_trivialKanFibration (F.obj i)).mp (hF i)
  let (i : I) : TrivialKanFibration (t.app i) := ht i
  let q := weightedSectionsMap (bousfieldKanWeight I) t
  have hq : TrivialKanFibration q := bousfieldKanMap_trivialKanFibration t
  have hT : IsTerminal (bousfieldKanHolim (selectionTerminalDiagram I)) :=
    selectionTerminalSections_isTerminal (bousfieldKanWeight I)
  intro n a
  have := hq.mem (boundary n).ι inferInstance
  let sq : CommSq a (boundary n).ι q (hT.from (Δ[n] : SSet.{u})) :=
    ⟨hT.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 一つの coherent な全選択を、全ての over 圏の nerve 上の自然な族へ戻す。 -/
def diagramSelectionAt {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})
    (v : (bousfieldKanHolim F) _⦋0⦌) : bousfieldKanWeight I ⟶ F :=
  (ρ_ (bousfieldKanWeight I)).inv ≫
    weightedSectionsUncurry ((SSet.unitHomEquiv (bousfieldKanHolim F)).symm v)

/-- 任意の単射上で既存の coherent な選択族を保ち、図式全体の選択族を補完できる。 -/
lemma contractibleDiagramSelections_relative_lifting {I : Type u} [SmallCategory I]
    (F : I ⥤ SSet.{u}) (hF : ∀ i, IsContractibleKan (F.obj i))
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ bousfieldKanHolim F) :
    ∃ b : T ⟶ bousfieldKanHolim F, j ≫ b = a := by
  have hp := (isContractibleKan_iff_trivialKanFibration _).mp
    (contractibleDiagramSelections_isContractibleKan F hF)
  have := hp.mem j inferInstance
  let sq : CommSq a j (terminal.from (bousfieldKanHolim F)) (terminal.from T) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.KST.SConstruction
