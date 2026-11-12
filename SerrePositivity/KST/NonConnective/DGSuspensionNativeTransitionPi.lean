module
public import SerrePositivity.KST.NonConnective.DGSuspensionShiftedTransition
public import SerrePositivity.KST.LocalizingInvariants.SpectrumNativeLoopPi
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：同じ dg 懸垂列の実隣接射を、構造辺の移動した整数 π 作用に比較する。
方針：Sp 正本の native loop 次数移動の自然同型を同じ反復回数だけ使う。
規約：明示構造辺に条件付き。一般の loop API や構造辺の存在は追加しない。
使われ方：K-7 d2 の自然性と d3 の非負次数での安定化の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance nativeTransitionSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance nativeTransitionSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

private def transitionLoopFunctor (m : ℕ) :=
  (hoFunctor.map (End.of OmegaSpectrum.nativeLoop.{w} ^ m).asHom).toFunctor

private def transitionLoopPiIso (m : ℕ) (j : ℤ) :
    transitionLoopFunctor.{w} m ⋙ SpectrumHo.piFunctor j ≅
      SpectrumHo.piFunctor (j + m) := by
  induction m with
  | zero =>
    have h : transitionLoopFunctor.{w} 0 = 𝟭 (hoFunctor.obj Sp.{w}) := by
      simp only [transitionLoopFunctor, pow_zero, End.one_asHom,
        CategoryTheory.Functor.map_id]
      rfl
    exact eqToIso (congrArg (fun F => F ⋙ SpectrumHo.piFunctor j) h) ≪≫
      Functor.leftUnitor _ ≪≫ eqToIso (by simp)
  | succ m ih =>
    have h : transitionLoopFunctor.{w} (m + 1) =
        (hoFunctor.map OmegaSpectrum.nativeLoop).toFunctor ⋙ transitionLoopFunctor m := by
      change (hoFunctor.map (End.of OmegaSpectrum.nativeLoop ^ (m + 1)).asHom).toFunctor =
        (hoFunctor.map OmegaSpectrum.nativeLoop ≫
          hoFunctor.map (End.of OmegaSpectrum.nativeLoop ^ m).asHom).toFunctor
      rw [← Functor.map_comp]
      simp only [pow_succ, End.mul_asHom]
    exact eqToIso (congrArg (fun F => F ⋙ SpectrumHo.piFunctor j) h) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ih ≪≫
        SpectrumHo.nativeLoopPiIso (j + m) ≪≫
          eqToIso (congrArg SpectrumHo.piFunctor (by push_cast; omega))

private theorem transitionPi_ofEq {x y x' y' : Sp.{w} _⦋0⦌}
    (e : Sp.Edge x y) (hx : x = x') (hy : y = y') (j : ℤ) :
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk (e.ofEq hx hy).toTruncated) j) ↔
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk e.toTruncated) j) := by
  cases hx
  cases hy
  rfl

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (A : PerfDGInput.{u, max (u + 1) v} R)
  (β : ∀ n : ℕ,
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))))

/-- 概要：同じ元の構造辺の始点で評価した反復 loop の次数移動。
方針：Sp 正本の自然同型を同じ反復段で評価する。
規約：対象と反復回数を変更しない。
使われ方：元の構造辺の作用との可換式の始点比較。 -/
@[no_expose] def dgSuspensionStructureLoopSourcePiIso (n : ℕ) (j : ℤ) :
    ((hoFunctor.map (End.of OmegaSpectrum.nativeLoop ^ n).asHom).toFunctor ⋙
      SpectrumHo.piFunctor j).obj (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))) ≅
    (SpectrumHo.piFunctor (j + n)).obj (HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))) :=
  (transitionLoopPiIso n j).app _

/-- 概要：同じ元の構造辺の終点で評価した反復 loop の次数移動。
方針：Sp 正本の自然同型を同じ反復段で評価する。
規約：終点は元の次段の一回 loop 頂点に固定する。
使われ方：元の構造辺の作用との可換式の終点比較。 -/
@[no_expose] def dgSuspensionStructureLoopTargetPiIso (n : ℕ) (j : ℤ) :
    ((hoFunctor.map (End.of OmegaSpectrum.nativeLoop ^ n).asHom).toFunctor ⋙
      SpectrumHo.piFunctor j).obj (HomotopyCategory.mk
        (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1)))))) ≅
    (SpectrumHo.piFunctor (j + n)).obj (HomotopyCategory.mk
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1)))))) :=
  (transitionLoopPiIso n j).app _

/-- 概要：明示構造辺に条件付きで、元の全一単体の π 作用は次数移動と可換。
方針：Sp 正本の自然性を同じ元の構造辺の類へ適用する。
規約：構造辺の供給の存在を主張しない。
使われ方：同じ反復 loop 後の実 BF 遷移の次数比較。 -/
theorem dgSuspensionStructureLoopPi_naturality (n : ℕ) (j : ℤ) :
    (SpectrumHo.piFunctor j).map
        ((hoFunctor.map (End.of OmegaSpectrum.nativeLoop ^ n).asHom).toFunctor.map
          (Truncated.HomotopyCategory.homMk (β n).toTruncated)) ≫
      (dgSuspensionStructureLoopTargetPiIso R s A n j).hom =
    (dgSuspensionStructureLoopSourcePiIso R s A n j).hom ≫
      (SpectrumHo.piFunctor (j + n)).map
        (Truncated.HomotopyCategory.homMk (β n).toTruncated) :=
  (transitionLoopPiIso n j).hom.naturality _

/-- 概要：明示構造辺に条件付きで、実隣接射の全単射性は元の辺の j+n 次数と同値。
方針：同じ辺の端点輸送を除き、自然な次数移動で可逆性を反映する。
規約：全段の Sp 引き戻し性は仮定しない。
使われ方：K-7 d2 から連結版 fibration による d3 への接続。 -/
theorem dgSuspensionNativeSequenceMap_bijective_iff_structure (n : ℕ) (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionNativeSequenceMap R s A β n) j) ↔
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk (β n).toTruncated) (j + n)) := by
  change Function.Bijective (OmegaSpectrum.homotopyMap
    (SpectrumHo.edgeMap (dgSuspensionNativeSequenceEdge R s A β n)) j) ↔ _
  rw [← SpectrumHo.piMap_edge]
  refine (transitionPi_ofEq _ _ _ j).trans ?_
  have h := NatIso.isIso_map_iff (transitionLoopPiIso n j)
    (Truncated.HomotopyCategory.homMk (β n).toTruncated)
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective] at h
  exact h

/-- 概要：明示構造辺に条件付きで、既存の次数座標の全単射性を元の構造辺へ移す。
方針：既存座標から実 BF 射への判定と自然な次数移動の判定を合成する。
規約：既存座標と新しい自然同型の等号は主張しない。
使われ方：元の整数次数の構造射による隣接安定化の判定。 -/
theorem dgSuspensionShiftedTransition_bijective_iff_structure (n : ℕ) (j : ℤ) :
    Function.Bijective (dgSuspensionShiftedTransition R s A β n j) ↔
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk (β n).toTruncated) (j + n)) :=
  (dgSuspensionShiftedTransition_bijective_iff R s A β n j).trans
    (dgSuspensionNativeSequenceMap_bijective_iff_structure R s A β n j)

/-- 概要：同じ実構造辺の移動次数での全単射性に条件付きで、元の連結比較は π 同型。
方針：Sp の自然な次数移動から実隣接射の安定化を導き、同じ余錐の零段の脚へ渡す。
規約：全段の Sp 引き戻し性を要求せず、構造辺の供給の存在も主張しない。
使われ方：K-7 d3 の連結版 fibration からの入力を受ける。 -/
theorem dgSuspensionConnectedComparison_bijective_of_structure (j : ℤ)
    (h : ∀ n : ℕ, Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk (β n).toTruncated) (j + n))) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionConnectedComparison R s A β) j) := by
  apply dgSuspensionConnectedComparison_bijective
  intro n
  exact (dgSuspensionNativeSequenceMap_bijective_iff_structure R s A β n j).mpr (h n)

end SerrePositivity.KST.NonConnective
