module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldIntervalDiagram
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：二点鎖上の simplicial replacement の通常の写像円柱表示。
方針：有限順序上の pushout の三つの部分を標準 1 単体と二つの係数値へ移す。
規約：これは厳密な単体集合の同型であり、全空間の同値判定は別に示す。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、Theorem 5.2.4.1（Tag 024N）、1 単体上の scaffold 比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：二点鎖上の simplicial replacement は係数の射の写像円柱となる pushout。
方針：末尾の一点とその係数値の同型、および nerve と標準 1 単体の同型で分解を移す。
規約：貼り合わせる端点は一であり、零端の係数値は prism の始点に残る。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、Theorem 5.2.4.1（Tag 024N）、scaffold 比較の初期帰納段階。 -/
@[kerodon 0366]
lemma scaffoldInterval_isPushout (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalMap F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalPrism F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F (ULift.up 1)) := by
  let K := F.obj (ULift.up 0)
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0 ⋙ F) (ULift.up 0)
  have : IsIso j :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift_isIso (C := ULift.{u} (Fin 1)) _ _
  have : IsIso (snd (nerve (ULift.{u} (Fin 1))) K) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nervePoint_snd_isIso (ULift.up (0 : Fin 1)) K
  let eA := asIso (snd (nerve (ULift.{u} (Fin 1))) K)
  let eB := (tensorRight K).mapIso (stdSimplex.isoNerve.{u} 1).symm
  let eC := (asIso j).symm
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteReplacement_isPushout 0 F).flip.of_iso eA eB eC (Iso.refl _)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalTail_endpoint K
  · change _ ≫ inv j = snd (nerve (ULift.{u} (Fin 1))) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalMap F
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalTail_assembly]
    change (snd (nerve (ULift.{u} (Fin 1))) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalMap F ≫ j) ≫ inv j = _
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · change _ ≫ 𝟙 _ =
      (stdSimplex.isoNerve.{u} 1).inv ▷ K ≫
        ((stdSimplex.isoNerve.{u} 1).hom ▷ K ≫ _)
    rw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0) F ≫ 𝟙 _ =
      inv j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F (ULift.up 1)
    rw [Category.comp_id]
    apply (cancel_epi j).1
    rw [IsIso.hom_inv_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalTail_constantLift F

/-- 概要：二点鎖上の simplicial replacement と係数の射の写像円柱の明示的な同型。
方針：標準の写像円柱の pushout と、構成した全空間の pushout の一意性を使う。
規約：円柱は標準 1 単体と F(0) の直積、終域部分は F(1)。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、写像円柱の普遍性からの scaffold の構成。 -/
@[kerodon 0366]
noncomputable def simplicialReplacementIntervalIso (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ≅
      pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalMap F) :=
  (scaffoldInterval_isPushout F).isoPushout

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
