module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Kan 値図式に対するモデル構造を使わない Brown 分解

概要：Hovey §1.1・§5 の積による Brown 分解を Kan 値図式に自然に構成する。
方針：ホーンの関手的小対象分解と Kan fibration の局所化同値の境界持ち上げを使う。
規約：単体集合にもその図式圏にも完全なモデル構造を置かない。
使われ方：射影 cofibrant 重みの錐の Kan 図式の不変性。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.SimplicialModel
open scoped _root_.SSet.modelCategoryQuillen

variable (K : Type u) [SmallCategory K]

local instance _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.instIsStableUnderBaseChangeSSetFibrations_serrePositivity : (fibrations SSet.{u}).IsStableUnderBaseChange := by
  rw [SSet.modelCategoryQuillen.fibrations_eq]
  infer_instance

private lemma evaluated_fst_fibration (F G : K ⥤ SSet.{u}) (k : K)
    (hG : SSet.KanComplex (G.obj k)) : Fibration ((prod.fst : F ⨯ G ⟶ F).app k) := by
  let ev := (CategoryTheory.evaluation K SSet.{u}).obj k
  have : IsFibrant (ev.obj G) := hG
  have : Fibration (prod.fst : ev.obj F ⨯ ev.obj G ⟶ ev.obj F) := inferInstance
  have : IsIso (prodComparison ev F G) := inferInstance
  change Fibration (ev.map (prod.fst : F ⨯ G ⟶ F))
  rw [← prodComparison_fst]
  infer_instance

private lemma evaluated_snd_fibration (F G : K ⥤ SSet.{u}) (k : K)
    (hF : SSet.KanComplex (F.obj k)) : Fibration ((prod.snd : F ⨯ G ⟶ G).app k) := by
  let ev := (CategoryTheory.evaluation K SSet.{u}).obj k
  have : IsFibrant (ev.obj F) := hF
  have : Fibration (prod.snd : ev.obj F ⨯ ev.obj G ⟶ ev.obj G) := inferInstance
  have : IsIso (prodComparison ev F G) := inferInstance
  change Fibration (ev.map (prod.snd : F ⨯ G ⟶ G))
  rw [← prodComparison_snd]
  infer_instance

/-- 概要：境界の右類の反転は Kan 値図式の各値の局所化同値の反転へ延びる。
方針：自然な積の Brown 分解の二つの射を境界の右類と証明する（Hovey §5）。
規約：弱同値は実際の anodyne 局所化での可逆性で読み、モデル構造は不要。
使われ方：重み付き錐へ両側の frame の比較を移す。 -/
lemma map_isIso_of_pointwiseKan {D : Type v} [Category.{w} D] (T : (K ⥤ SSet.{u}) ⥤ D)
    (hT : ∀ {F G : K ⥤ SSet.{u}} (p : F ⟶ G),
      (∀ k, SSet.modelCategoryQuillen.I.rlp (p.app k)) → IsIso (T.map p))
    {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k))) : IsIso (T.map f) := by
  let d := (AnodyneKanReplacement.factorization.functorCategory K).factorizationData
    (prod.lift (𝟙 F) f)
  let r : d.Z ⟶ F := d.p ≫ prod.fst
  let p : d.Z ⟶ G := d.p ≫ prod.snd
  have hir : d.i ≫ r = 𝟙 F := by
    dsimp only [r]
    rw [← Category.assoc, d.fac, prod.lift_fst]
  have hip : d.i ≫ p = f := by
    dsimp only [p]
    rw [← Category.assoc, d.fac, prod.lift_snd]
  have hirIso (k : K) : IsIso (AnodyneHomotopy.anodyneQ.map (r.app k)) := by
    have : IsIso (AnodyneHomotopy.anodyneQ.map (d.i.app k)) :=
      Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _ (d.hi k)
    have he : AnodyneHomotopy.anodyneQ.map (d.i.app k) ≫
        AnodyneHomotopy.anodyneQ.map (r.app k) = 𝟙 _ := by
      rw [← Functor.map_comp, ← NatTrans.comp_app, hir, NatTrans.id_app,
        CategoryTheory.Functor.map_id]
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (d.i.app k) ≫
        AnodyneHomotopy.anodyneQ.map (r.app k)) := he.symm ▸ inferInstanceAs (IsIso (𝟙 _))
    exact (isIso_comp_left_iff _ _).mp hc
  have hipIso (k : K) : IsIso (AnodyneHomotopy.anodyneQ.map (p.app k)) := by
    have : IsIso (AnodyneHomotopy.anodyneQ.map (d.i.app k)) :=
      Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _ (d.hi k)
    have he : AnodyneHomotopy.anodyneQ.map (d.i.app k) ≫
        AnodyneHomotopy.anodyneQ.map (p.app k) =
      AnodyneHomotopy.anodyneQ.map (f.app k) := by
      rw [← Functor.map_comp, ← NatTrans.comp_app, hip]
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (d.i.app k) ≫
        AnodyneHomotopy.anodyneQ.map (p.app k)) := he.symm ▸ hf k
    exact (isIso_comp_left_iff _ _).mp hc
  have hr (k : K) : SSet.modelCategoryQuillen.I.rlp (r.app k) := by
    have : Fibration (d.p.app k) := (SSet.modelCategoryQuillen.fibration_iff _).mpr (d.hp k)
    have : Fibration ((prod.fst : F ⨯ G ⟶ F).app k) := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluated_fst_fibration K F G k (hG k)
    have hrf : Fibration (r.app k) := by
      dsimp only [r, NatTrans.comp_app]
      infer_instance
    have := hF k
    exact KanFibrationLocalizedLifting.boundary_rlp _
      ((SSet.modelCategoryQuillen.fibration_iff _).mp hrf)
      ((SSet.modelCategoryQuillen.fibration_iff _).mp (show IsFibrant (F.obj k) from inferInstance))
      (hirIso k)
  have hp (k : K) : SSet.modelCategoryQuillen.I.rlp (p.app k) := by
    have : Fibration (d.p.app k) := (SSet.modelCategoryQuillen.fibration_iff _).mpr (d.hp k)
    have : Fibration ((prod.snd : F ⨯ G ⟶ G).app k) := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluated_snd_fibration K F G k (hF k)
    have hpf : Fibration (p.app k) := by
      dsimp only [p, NatTrans.comp_app]
      infer_instance
    have := hG k
    exact KanFibrationLocalizedLifting.boundary_rlp _
      ((SSet.modelCategoryQuillen.fibration_iff _).mp hpf)
      ((SSet.modelCategoryQuillen.fibration_iff _).mp (show IsFibrant (G.obj k) from inferInstance))
      (hipIso k)
  have : IsIso (T.map r) := hT r hr
  have : IsIso (T.map p) := hT p hp
  have hi : T.map d.i ≫ T.map r = 𝟙 _ := by rw [← T.map_comp, hir, T.map_id]
  have he : T.map d.i = inv (T.map r) := by
    apply (cancel_mono (T.map r)).mp
    simpa only [IsIso.inv_hom_id] using hi
  have : IsIso (T.map d.i) := by rw [he]; infer_instance
  rw [← hip, T.map_comp]
  infer_instance

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
