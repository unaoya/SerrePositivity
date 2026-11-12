module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FibrationTotalPositive
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FibrationComponentTransport

/-!
概要：Kan fibration の底と fiber から全空間の連結成分および全次数を比較する。
方針：単射性は連結写像、全射性は任意の底の頂点上の fiber の成分から得る。
規約：空の fiber の扱いを全基点 π_* 条件の外に明示する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、Sp の引き戻しの Ω 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：可換正方形の任意の底の頂点上で誘導される fiber 間の射。
方針：包含と全空間の射の合成を標的の fiber へ持ち上げる。
規約：源の fiber が非空であることを要求しない。
使われ方：空の fiber も含む連結成分の全射性を指定する。 -/
def fibrationFiberMapBase {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p' (g.app _ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p' (g.app _ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b ≫ f) (by
    rw [Category.assoc, ← comm, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, const_comp])

/-- 概要：任意の底の頂点上の fiber 射は包含後に全空間の射と可換。
方針：fiber への持ち上げの第一成分の計算を使う。
規約：Kan 性や fibration 性は不要。
使われ方：任意の fiber の連結成分の自然性。 -/
lemma fibrationFiberMapBase_ι {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) :
    fibrationFiberMapBase p p' f g comm b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (g.app _ b) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b ≫ f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι ..

/-- 概要：底の π_* 同型と非空 fiber の成分の単射性は全空間の成分の単射性を導く。
方針：底で同じ成分に戻し、連結写像の自然性と基本群の全射性で fiber の差を消す。
規約：fiber の単射性は全空間の各頂点の像の上だけで要求する。
使われ方：Sp の引き戻しの零次数比較の単射性。 -/
lemma fibrationTotal_piZero_injective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g)
    (hF : ∀ e : E _⦋0⦌, Function.Injective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e))) :
    Function.Injective (mapπ₀ f) := by
  intro a c hac
  obtain ⟨e, rfl⟩ := π₀.mk_surjective a
  have hp : mapπ₀ p c = π₀.mk (p.app _ e) := by
    apply (hg.piZero_bijective_at (p.app _ e)).injective
    calc
      _ = mapπ₀ p' (mapπ₀ f c) := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square p p' f g comm c
      _ = mapπ₀ p' (mapπ₀ f (π₀.mk e)) := congrArg (mapπ₀ p') hac.symm
      _ = mapπ₀ g (mapπ₀ p (π₀.mk e)) :=
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square p p' f g comm (π₀.mk e)).symm
      _ = _ := rfl
  obtain ⟨s, hs⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentFiber_exact p e c).mp hp
  let φ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e
  have hφ : mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (p'.app _ (f.app _ e))) (mapπ₀ φ s) = π₀.mk (f.app _ e) := by
    calc
      _ = mapπ₀ f (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) s) :=
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _ φ f (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e).symm s).symm
      _ = mapπ₀ f c := congrArg (mapπ₀ f) hs
      _ = mapπ₀ f (π₀.mk e) := hac.symm
      _ = _ := rfl
  obtain ⟨β', hβ'⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_exact p' (f.app _ e) _ rfl (mapπ₀ φ s)).mp hφ
  obtain ⟨β, hβ⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism 0 g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e)).surjective β'
  have hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p e (p.app _ e) rfl β = s := by
    apply hF e
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_natural p p' f g comm e _ rfl _ rfl φ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e) β).trans
        ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p' (f.app _ e) _ rfl) hβ).trans hβ')
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_exact p e _ rfl s).mpr ⟨β, hδ⟩
  exact hc.symm.trans hs

/-- 概要：底の成分の全射性と全ての fiber の成分の全射性は全空間の成分の全射性を導く。
方針：底の成分を選び、任意の底の頂点上の fiber に成分を移してから持ち上げる。
規約：全ての底の頂点を扱い、空の fiber の全射性を省略しない。
使われ方：Sp の引き戻しの零次数比較の全射性。 -/
lemma fibrationTotal_piZero_surjective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : Function.Surjective (mapπ₀ g))
    (hF : ∀ b : B _⦋0⦌, Function.Surjective (mapπ₀ (fibrationFiberMapBase p p' f g comm b))) :
    Function.Surjective (mapπ₀ f) := by
  intro a'
  obtain ⟨b, hb⟩ := hg (mapπ₀ p' a')
  obtain ⟨b, rfl⟩ := π₀.mk_surjective b
  obtain ⟨c', hc'⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibration_componentFiber_exists p' (g.app _ b) a' hb.symm
  obtain ⟨c, hc⟩ := hF b c'
  refine ⟨mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) c, ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _ _ f (fibrationFiberMapBase_ι p p' f g comm b).symm c).trans
    ((congrArg (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (g.app _ b))) hc).trans hc')

/-- 概要：底と非空 fiber の π_* 比較および全 fiber の成分の全射性から全空間の π_* 同型を得る。
方針：零次数は成分の単射性・全射性、正次数は基点付き集合へ続く五項補題を使う。
規約：空の fiber の検査を全基点の条件とは別の明示前提として保持する。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻し比較へ渡す全空間の判定。 -/
lemma fibrationTotal_piIsomorphism {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g)
    (hF : ∀ e : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e))
    (hF₀ : ∀ b : B _⦋0⦌,
      Function.Surjective (mapπ₀ (fibrationFiberMapBase p p' f g comm b))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  intro e n
  cases n with
  | zero =>
    apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero.map_bijective_iff_piZero f rfl).mpr
    exact ⟨fibrationTotal_piZero_injective p p' f g comm hg
      (fun e ↦ ((hF e).piZero_bijective_at (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)).injective),
      fibrationTotal_piZero_surjective p p' f g comm
        (hg.piZero_bijective_at (p.app _ e)).surjective hF₀⟩
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationTotal_positive_bijective p p' f g comm hg e (hF e) n

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
