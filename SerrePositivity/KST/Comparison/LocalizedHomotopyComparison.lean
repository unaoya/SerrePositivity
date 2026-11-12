module

public import SerrePositivity.KST.Spectra.AnodyneHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 局所化同型から K-L9 のホモトピー類への比較

概要：Kan 複体間の局所化可逆な射は全基点・全次数のホモトピー類の全単射を誘導する。
方針：anodyne・Kan fibration 分解と局所化による右因子の持ち上げ性の検出を用いる。
規約：Segal 1974 Proposition 1.5 の比較の出力を K-L9 の実際の π_n に渡す。
使われ方：KST Lemma 2.13 の次数移動。π_n の定義と不変性は K-L9 から借りる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits HomotopicalAlgebra SSet
open scoped Simplicial
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

/--
概要：局所化可逆な Kan 複体間の射は K-L9 の全ホモトピー類の同型である。
方針：分解の左因子には anodyne の不変性、右因子には単射 RLP の不変性を使う。
規約：全自然数次数と全基点を含む。新たな弱同値の公理を仮定しない。
使われ方：標準群完備化写像の具体的なホモトピー類への接続。
-/
theorem kanPiIsomorphism_of_localized_isIso {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    (f : A ⟶ B) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  let F := AnodyneKanReplacement.factorization
  let i : A ⟶ F.Z.obj (Arrow.mk f) := F.i.app (Arrow.mk f)
  let p : F.Z.obj (Arrow.mk f) ⟶ B := F.p.app (Arrow.mk f)
  have hi : anodyneExtensions i := F.hi _
  have hp : J.rlp p := F.hp _
  have fac : i ≫ p = f := F.fac_app
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).2 hp
  have : KanComplex (F.Z.obj (Arrow.mk f)) := by
    change Fibration (terminal.from (F.Z.obj (Arrow.mk f)))
    rw [show terminal.from (F.Z.obj (Arrow.mk f)) = p ≫ terminal.from B from
      terminal.hom_ext _ _]
    infer_instance
  let Q := AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map i) := (Localization.inverts Q anodyneExtensions) i hi
  have hQp : IsIso (Q.map p) := by
    have hfac : Q.map i ≫ Q.map p = Q.map f :=
      (Q.map_comp i p).symm.trans (congrArg Q.map fac)
    have : IsIso (Q.map i ≫ Q.map p) := hfac.symm ▸ hf
    exact (isIso_comp_left_iff (Q.map i) (Q.map p)).1 this
  have hr := KanFibrationLocalizedLifting.of_localized_isIso p hp
    ((SSet.modelCategoryQuillen.fibration_iff _).1
      (inferInstance : Fibration (terminal.from B))) hQp
  exact fac ▸ (Spectra.kanPiIsomorphism_of_anodyne i hi).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight p hr)

/--
概要：局所化可逆な Kan 複体間の射のホモトピー類の具体的な全単射。
方針：K-L9 の誘導写像と証明した全単射性から同値を作る。
規約：像の基点は射による実際の像とする。
使われ方：ループの次数移動との同値の合成。
-/
@[kerodon 00ZL]
def kanHomotopyEquivOfLocalizedIso {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    (f : A ⟶ B) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f))
    (a : A _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy A n a ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy B n (f.app _ a) :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl)
    (kanPiIsomorphism_of_localized_isIso f hf a n)

end SerrePositivity.KST.Comparison
