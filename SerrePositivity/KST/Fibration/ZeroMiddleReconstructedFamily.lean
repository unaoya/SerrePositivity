module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSReconstruction

/-!
概要：同じ実長 Hom 入力から、元の二短辺を保つ制御二胞体族を取り出す。
方針：Ind-S (9) の encode の指定頂点を実族へ戻し、同じ読出しの厳密切断式を使う。
規約：供給命題に条件付き。実長 Hom はデータ引数で、入力空間の存在は追加仮定にしない。
使われ方：K-6 c4 の指定パラメータ族を実二胞体と全 Hom の回収へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1}) (h9 : zeroMiddleControlledTriangleSupply.{u})
  (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌)

/-- 概要：同じ実長 Hom 入力の encode 像を二胞体族空間の指定点とする。
方針：同じ再構成写像の零次作用だけを取り出す。
規約：同じ境界 fiber の点を保持する。
使われ方：実制御二胞体族と長 Hom 読出しの共通入力。 -/
def zeroMiddleReconstructedFamilyPoint :
    (zeroMiddleFullSReconstructionTriangleSpace s hZ K) _⦋0⦌ :=
  (zeroMiddleFullSReconstructionEncode s hZ K h9).app (Opposite.op ⦋0⦌) ℓ

/-- 概要：同じ入力から得る全パラメータ制御二胞体族。
方針：元の encode 像の関手頂点をそのまま実全族へ戻す。
規約：三角形を各パラメータ点で選び直さない。供給命題に条件付き。
使われ方：K-6 c4 の指定全長 Hom の実再構成。 -/
def zeroMiddleReconstructedFamily : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
    (zeroMiddleReconstructedFamilyPoint s hZ K h9 ℓ).val

/-- 概要：再構成した実族の頂点表示は同じ元の encode 像。
方針：関手頂点の標準順逆の回収を使う。
規約：元の全二胞体族を厳密に保持する。
使われ方：固定二短辺の制限と読出しを同じ実族へ戻す。 -/
theorem zeroMiddleReconstructedFamily_vertex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleReconstructedFamily s hZ K h9 ℓ) =
      (zeroMiddleReconstructedFamilyPoint s hZ K h9 ℓ).val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _

/-- 概要：同じ再構成族は元の二短辺の実ホーン全族を厳密回収する。
方針：元の境界 fiber の指定点の条件を実全族へ戻す。
規約：端点だけや個々の辺のホモトピー類で代用しない。
使われ方：指定長 Hom の制御二胞体を実三単体族へ渡す前の境界確認。 -/
theorem zeroMiddleReconstructedFamily_horn :
    ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ zeroMiddleReconstructedFamily s hZ K h9 ℓ =
      zeroMiddleFullSReconstructionHorn s hZ K := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((horn 2 (1 : Fin 3)).ι ▷ K) ≫
    zeroMiddleReconstructedFamily s hZ K h9 ℓ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSReconstructionHorn s hZ K)
  calc
    _ = ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleReconstructedFamily s hZ K h9 ℓ)) := rfl
    _ = _ := congrArg
      (((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).app (Opposite.op ⦋0⦌))
      (zeroMiddleReconstructedFamily_vertex s hZ K h9 ℓ)
    _ = _ := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using
        (zeroMiddleReconstructedFamilyPoint s hZ K h9 ℓ).property

/-- 概要：同じ encode 像の全長 Hom 読出しは元の実入力点そのもの。
方針：全族の厳密切断式を同じ指定頂点で評価する。
規約：各パラメータ点の同型へ弱めない。
使われ方：元の全パラメータの指定長 Hom の回収。 -/
theorem zeroMiddleReconstructedFamilyPoint_read :
    (zeroMiddleFullSReconstructionRead s hZ K h9).app (Opposite.op ⦋0⦌)
      (zeroMiddleReconstructedFamilyPoint s hZ K h9 ℓ) = ℓ :=
  congrArg (fun f => f.app (Opposite.op ⦋0⦌) ℓ)
    (zeroMiddleFullSReconstructionEncode_read s hZ K h9)

/-- 概要：同じ制御族の各指定点の全 native Hom は指定実入力の読出しそのもの。
方針：同じ全族切断式で元の入力へ戻してから、供給の native Hom 回収を使う。
規約：同じ実二胞体族を保持し、各点で再構成を選び直さない。
使われ方：K-6 c4 の指定全長 Hom と実制御上側の照合。 -/
theorem zeroMiddleReconstructedFamily_longHom (k : K _⦋0⦌) :
    let P := CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
    let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm ℓ.val
    let st := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
      ((curry (zeroMiddleReconstructedFamily s hZ K h9 ℓ)).app (Opposite.op ⦋0⦌) k))
    HEq (Lt.app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (st.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have h := zeroMiddleFullSReconstructionRead_recovery s hZ K h9
    (zeroMiddleReconstructedFamilyPoint s hZ K h9 ℓ) k
  dsimp only [zeroMiddleFullSReconstructionRecovery] at h
  simpa only [zeroMiddleReconstructedFamilyPoint_read, zeroMiddleReconstructedFamily] using h

end SerrePositivity.KST.Fibration
