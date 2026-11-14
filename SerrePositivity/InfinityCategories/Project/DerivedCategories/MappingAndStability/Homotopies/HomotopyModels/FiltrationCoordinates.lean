module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SplitSequence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SphereBasis

/-! # Semifree filtration の次数ごとの直和座標

概要：既存の semifree filtration を評価し、各次数で初期段と商の直和へ同一視する。
方針：次数付き分裂と評価が保存する余極限を分裂列の線形同型に適用する。
規約：元の semifree 定義を保持する。使われ方：高さ付き基底の必要性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped DirectSum
variable {S : Type u} [CommRing S] {M : ModuleCategory S PUnit.{1}}
namespace SemifreeFiltration
variable (F : ModuleSemifreeFiltration S PUnit.{1} M)

/-- 概要：filtration の一つの次数を分裂加群列として読む。
方針：唯一の対象で評価してから複体の次数を評価する。
規約：切断は元の次数付き分裂。使われ方：直和座標の構成。 -/
def splitSequence (k : ℤ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SplitModuleSequence S where
  stage n := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeStage S F n).X k
  quotient n := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeQuotient S F n).X k
  inclusion n := ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.transition n)).f k
  projection n := ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.quotientMap n)).f k
  retraction n := (F.split n).retraction PUnit.unit k
  section_ n := (F.split n).section_ PUnit.unit k
  inclusion_retraction n := (F.split n).inclusion_retraction PUnit.unit k
  section_projection n := (F.split n).section_projection PUnit.unit k
  section_retraction n := (F.split n).section_retraction PUnit.unit k
  inclusion_projection n := by
    have h := congrArg (fun f => ((moduleEvaluation S PUnit.{1} PUnit.unit).map f).f k)
      (F.split n).inclusion_projection
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
      CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f] using h
  decomposition n := (F.split n).decomposition PUnit.unit k

/-- 概要：次数評価された filtration の cocone。
方針：元の cocone を二つの評価関手で写す。
規約：図式比較は隣接段で恒等。使われ方：余極限の直和表示。 -/
def degreeCocone (k : ℤ) : Cocone (Functor.ofSequence ((splitSequence F) k).inclusion) where
  pt := ((moduleEvaluation S PUnit.{1} PUnit.unit).obj F.cocone.pt).X k
  ι := NatTrans.ofSequence
    (fun n => ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.cocone.ι.app n)).f k)
    (by
      intro n
      rw [Functor.ofSequence_map_homOfLE_succ]
      have h := congrArg (fun f => ((moduleEvaluation S PUnit.{1} PUnit.unit).map f).f k)
        (F.cocone.w (homOfLE (Nat.le_succ n)))
      rw [Functor.ofSequence_map_homOfLE_succ] at h
      simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
      change ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.transition n)).f k ≫
        ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.cocone.ι.app (n + 1))).f k =
          ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.cocone.ι.app n)).f k ≫ 𝟙 _
      rw [Category.comp_id]
      exact h)

/-- 概要：評価した列の図式は評価された元の図式と自然同型である。
方針：隣接射の一致を使う。
規約：対象成分は恒等。使われ方：余極限保存の転送。 -/
def degreeDiagramIso (k : ℤ) :
    Functor.ofSequence F.transition ⋙ moduleEvaluation S PUnit.{1} PUnit.unit ⋙
      HomologicalComplex.eval (ModuleCat S) (.up ℤ) k ≅
      Functor.ofSequence ((splitSequence F) k).inclusion :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (NatTrans.ofSequence
      (F := Functor.ofSequence F.transition ⋙ moduleEvaluation S PUnit.{1} PUnit.unit ⋙
        HomologicalComplex.eval (ModuleCat S) (.up ℤ) k)
      (G := Functor.ofSequence (splitSequence F k).inclusion)
      (fun _ => 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rfl)).naturality f)

/-- 概要：次数評価された filtration の cocone は余極限である。
方針：二つの評価関手の余極限保存を用い、図式の自然同型で移す。
規約：新たな余極限の存在仮定は不要。使われ方：直和座標の線形同型。 -/
def degreeIsColimit (k : ℤ) : IsColimit ((degreeCocone F) k) := by
  let ev := moduleEvaluation S PUnit.{1} PUnit.unit ⋙
    HomologicalComplex.eval (ModuleCat S) (.up ℤ) k
  let h := isColimitOfPreserves ev F.isColimit
  apply (IsColimit.precomposeHomEquiv ((degreeDiagramIso F) k) ((degreeCocone F) k)).1
  apply h.ofIsoColimit
  refine Cocone.ext (Iso.refl (ev.obj F.cocone.pt)) (fun n => ?_)
  change ev.map (F.cocone.ι.app n) ≫ 𝟙 _ =
    (𝟙 _ ≫ ((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.cocone.ι.app n)).f k)
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- 概要：元の加群の一つの次数と初期段・商の直和との線形同型。
方針：filtration の頂点同型を戻してから分裂列の座標を取る。
規約：成分零は初期段、成分 n+1 は商 n。使われ方：semibasis の基底。 -/
def degreeLinearEquiv (k : ℤ) :
    ((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).X k ≃ₗ[S]
      ⨁ n, ((splitSequence F) k).piece n :=
  ((HomologicalComplex.eval (ModuleCat S) (.up ℤ) k).mapIso
    ((moduleEvaluation S PUnit.{1} PUnit.unit).mapIso F.iso)).toLinearEquiv.symm.trans
      (((splitSequence F) k).linearEquiv ((degreeCocone F) k) ((degreeIsColimit F) k))

/-- 概要：直和の各成分の自由性。
方針：初期段と各商の sphere 表示を次数評価する。
規約：任意の整数次数。使われ方：直和基底の選択。 -/
theorem piece_free (k : ℤ) (n : ℕ) : Module.Free S (((splitSequence F) k).piece n) := by
  cases n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spherePresentation_degree_free S F.initial k
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spherePresentation_degree_free S (F.quotientPresentation n) k

/-- 概要：filtration の各段から元の複体への包含。
方針：cocone の脚と頂点同型を評価する。
規約：ここでの包含は鎖写像。使われ方：微分の座標計算。 -/
def stageLeg (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeStage S F n ⟶
    (moduleEvaluation S PUnit.{1} PUnit.unit).obj M :=
  (moduleEvaluation S PUnit.{1} PUnit.unit).map (F.cocone.ι.app n ≫ F.iso.hom)

/-- 概要：段から来る元の直和座標は有限段の座標である。
方針：頂点同型を消去し、分裂列の脚の座標公式を使う。
規約：次数ごとの等式。使われ方：微分の高さ上限。 -/
theorem degreeLinearEquiv_stageLeg (k : ℤ) (n : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeStage S F n).X k) :
    degreeLinearEquiv F k (((stageLeg F n).f k).hom x) =
      (splitSequence F k).coordinates n x := by
  let e := (HomologicalComplex.eval (ModuleCat S) (.up ℤ) k).mapIso
    ((moduleEvaluation S PUnit.{1} PUnit.unit).mapIso F.iso)
  change (splitSequence F k).linearEquiv (degreeCocone F k) (degreeIsColimit F k)
    (e.toLinearEquiv.symm (((stageLeg F n).f k).hom x)) = _
  have hx : ((stageLeg F n).f k).hom x =
      e.toLinearEquiv (((degreeCocone F k).ι.app n).hom x) := by
    dsimp only [stageLeg]
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    rfl
  rw [hx, LinearEquiv.symm_apply_apply]
  exact (splitSequence F k).linearEquiv_leg _ _ n x

/-- 概要：直和成分の逆像は商の切断を cocone へ送ったものである。
方針：線形同型の逆と直和の復元写像を展開する。
規約：零成分の切断は初期段。使われ方：基底ベクトルの微分計算。 -/
theorem degreeLinearEquiv_symm_lof (k : ℤ) (n : ℕ)
    (x : (splitSequence F k).piece n) :
    (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) n x) =
    (((moduleEvaluation S PUnit.{1} PUnit.unit).map F.iso.hom).f k).hom
      ((splitSequence F k).pieceMap (degreeCocone F k) n x) := by
  change (((moduleEvaluation S PUnit.{1} PUnit.unit).map F.iso.hom).f k).hom
    ((splitSequence F k).assemble (degreeCocone F k)
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) n x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SplitModuleSequence.assemble, DirectSum.toModule_lof]

/-- 概要：直和の各成分の基底を選ぶ。
方針：自由 sphere 表示から得た自由性を用いる。
規約：添字は係数環と同じ宇宙。使われ方：filtration の基底。 -/
def pieceBasis (k : ℤ) (n : ℕ) :
    Module.Basis (letI := piece_free F k n;
      Module.Free.ChooseBasisIndex S ((splitSequence F k).piece n)) S
      ((splitSequence F k).piece n) := by
  letI := piece_free F k n
  exact Module.Free.chooseBasis S ((splitSequence F k).piece n)

/-- 概要：各段の商の基底をまとめた元の複体の次数付き基底。
方針：直和基底を座標同型の逆で移す。
規約：添字の第一成分は段番号。使われ方：semibasis の高さ関数。 -/
def basis (k : ℤ) :=
  (DFinsupp.basis (pieceBasis F k)).map (degreeLinearEquiv F k).symm

/-- 概要：filtration の基底の座標は直和座標の対応する成分の基底座標である。
方針：直和基底の表現同型を展開する。
規約：添字は段番号とその成分の基底添字。使われ方：高さ下降条件。 -/
theorem basis_repr (k : ℤ)
    (x : ((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).X k)
    (a : Σ n, letI := piece_free F k n;
      Module.Free.ChooseBasisIndex S ((splitSequence F k).piece n)) :
    (basis F k).repr x a =
      (pieceBasis F k a.1).repr (degreeLinearEquiv F k x a.1) a.2 := by
  change (sigmaFinsuppLequivDFinsupp S).symm
    (DFinsupp.mapRange (fun n => (pieceBasis F k n).repr)
      (fun n => map_zero _) (degreeLinearEquiv F k x)) a = _
  simp

/-- 概要：filtration 基底のベクトルの具体形。
方針：直和基底の単一成分表示を座標同型で戻す。
規約：基底の段番号を保つ。使われ方：微分の前段への帰属。 -/
theorem basis_apply (k : ℤ)
    (a : Σ n, letI := piece_free F k n;
      Module.Free.ChooseBasisIndex S ((splitSequence F k).piece n)) :
    basis F k a = (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) a.1
        (pieceBasis F k a.1 a.2)) := by
  apply (degreeLinearEquiv F k).injective
  simp only [basis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  apply (DFinsupp.basis (pieceBasis F k)).repr.injective
  refine (congrArg (DFinsupp.basis (pieceBasis F k)).repr
    ((degreeLinearEquiv F k).apply_symm_apply ((DFinsupp.basis (pieceBasis F k)) a))).trans ?_
  refine ((DFinsupp.basis (pieceBasis F k)).repr_self a).trans ?_
  change Finsupp.single a 1 =
    (sigmaFinsuppLequivDFinsupp S).symm
      (DFinsupp.mapRange (fun n => (pieceBasis F k n).repr) (fun n => map_zero _)
        (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) a.1
          (pieceBasis F k a.1 a.2)))
  change Finsupp.single a 1 =
    (sigmaFinsuppLequivDFinsupp S).symm
      (DFinsupp.mapRange (fun n => (pieceBasis F k n).repr) (fun n => map_zero _)
        (DFinsupp.single a.1 (pieceBasis F k a.1 a.2)))
  simp only [DFinsupp.mapRange_single, Module.Basis.repr_self]
  exact (sigmaFinsuppEquivDFinsupp.symm_apply_apply (Finsupp.single a (1 : S))).symm.trans
    (congrArg sigmaFinsuppEquivDFinsupp.symm (sigmaFinsuppEquivDFinsupp_single a (1 : S)))

/-- 概要：初期直和成分の逆像は初期段の脚である。
方針：直和成分の逆像公式と関手の合成保存を使う。
規約：成分零。使われ方：初期基底の微分零。 -/
theorem degreeLinearEquiv_symm_lof_zero (k : ℤ)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeStage S F 0).X k) :
    (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) 0 x) =
      ((stageLeg F 0).f k).hom x := by
  rw [degreeLinearEquiv_symm_lof]
  dsimp only [stageLeg]
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
  rfl

/-- 概要：商の直和成分の逆像は切断と段の脚の合成である。
方針：直和成分の逆像公式と関手の合成保存を使う。
規約：成分 n+1 は商 n。使われ方：商基底の微分の高さ。 -/
theorem degreeLinearEquiv_symm_lof_succ (k : ℤ) (n : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeQuotient S F n).X k) :
    (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) (n + 1) x) =
      ((stageLeg F (n + 1)).f k).hom (((F.split n).section_ PUnit.unit k).hom x) := by
  rw [degreeLinearEquiv_symm_lof]
  dsimp only [stageLeg]
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
  rfl

/-- 概要：初期段から来る元の微分は零である。
方針：脚が鎖写像であり、初期段が自由 sphere 表示を持つことを使う。
規約：任意の初期段の元。使われ方：高さ零の微分。 -/
theorem stageLeg_zero_d (k : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeStage S F 0).X k) :
    ((((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).d k (k + 1)).hom)
      (((stageLeg F 0).f k).hom x) = 0 := by
  have h := congrArg (fun f => f.hom x) ((stageLeg F 0).comm k (k + 1))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spherePresentation_d S F.initial] at h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, zero_comp, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- 概要：第 n 商の切断の微分の直和座標は n を超える成分で零である。
方針：微分と商射の可換性により新しい商座標が零となり、前段の座標へ帰着する。
規約：商射は鎖写像、切断は線形のみ。使われ方：semibasis の厳密な高さ下降。 -/
theorem section_d_coordinates (k : ℤ) (n j : ℕ) (hj : n < j)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeQuotient S F n).X k) :
    degreeLinearEquiv F (k + 1)
      ((((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).d k (k + 1)).hom
        (((stageLeg F (n + 1)).f k).hom
          (((F.split n).section_ PUnit.unit k).hom x))) j = 0 := by
  let y := (((F.split n).section_ PUnit.unit k).hom x)
  let z := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeStage S F (n + 1)).d k (k + 1)).hom y
  have hd := congrArg (fun f => f.hom y) ((stageLeg F (n + 1)).comm k (k + 1))
  change (((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).d k (k + 1)).hom
    (((stageLeg F (n + 1)).f k).hom y) =
      ((stageLeg F (n + 1)).f (k + 1)).hom z at hd
  rw [hd, degreeLinearEquiv_stageLeg]
  have hq := congrArg (fun f => f.hom y)
    (((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.quotientMap n)).comm k (k + 1))
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifreeQuotient S F n).d k (k + 1)).hom
    ((((moduleEvaluation S PUnit.{1} PUnit.unit).map (F.quotientMap n)).f k).hom y) =
      ((splitSequence F (k + 1)).projection n).hom z at hq
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spherePresentation_d S (F.quotientPresentation n)] at hq
  have hqz : ((splitSequence F (k + 1)).projection n).hom z = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, comp_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply] using hq.symm
  change ((splitSequence F (k + 1)).coordinates n
      (((splitSequence F (k + 1)).retraction n).hom z) +
    DirectSum.lof S ℕ (fun i => (splitSequence F (k + 1)).piece i) (n + 1)
      (((splitSequence F (k + 1)).projection n).hom z)) j = 0
  rw [hqz, map_zero, add_zero]
  exact (splitSequence F (k + 1)).coordinates_apply_eq_zero n j hj _

end SemifreeFiltration
end SerrePositivity.InfinityCategories.Project.DerivedCategories
