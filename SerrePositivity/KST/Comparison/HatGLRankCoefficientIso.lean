module

public import SerrePositivity.KST.Comparison.HatGLCoefficientStabilization
public import SerrePositivity.KST.Comparison.StableHatGLHomotopyGroupColimit

/-!
# rank の群の図式の係数表示の自然同型

概要：有限 rank の ĜL の正次数の群の図式を係数行列群の図式と自然に同定する。
方針：自然数の隣接射での可換性から全ての順序射での自然性を得て、添字の宇宙を戻す。
規約：KST Lemma 2.13 の安定化後の群の比較の入力。
使われ方：群の図式の実際の余極限の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite SSet
open scoped Simplicial

/--
概要：自然数の rank で表示した既存の正次数の群の図式。
方針：宇宙を揃えた図式を rank の圏同値の逆で前合成する。
規約：K-L9 の群と誘導写像を保持する。
使われ方：隣接する rank の自然性による自然同型の構成。
-/
def nativeHatGLHomotopyGroupDiagram (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    ℕ ⥤ GrpCat.{u} :=
  liftedRankEquivalence.inverse ⋙ stableHatGLHomotopyGroupDiagram A n

/--
概要：隣接する rank の群の図式の射は実際の安定化の誘導準同型である。
方針：rank の圏同値の往復と順序列の隣接射を計算する。
規約：単位基点を保つ。
使われ方：有限 rank の係数表示の可換性を図式の自然性へ渡す。
-/
theorem nativeHatGLHomotopyGroupDiagram_map_succ (A : SimplicialObject RingCat.{u})
    (n r : ℕ) :
    (nativeHatGLHomotopyGroupDiagram A n).map (homOfLE (r.le_add_right 1)) =
      GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (hatGLSpaceStabilization A r)
        (hatGLSpaceStabilization_unit A r)) := by
  let f := (hatGLRankSequence A).map (homOfLE (r.le_add_right 1))
  have hf : (Functor.whiskerRight f (forget MonCat)).app (op ⦋0⦌)
      (1 : hatGLSubmonoid A r 0) = (1 : hatGLSubmonoid A (r + 1) 0) :=
    map_one (f.app (op ⦋0⦌)).hom
  have : KanComplex ((hatGLRankSequence A).obj r ⋙ forget MonCat) :=
    inferInstanceAs (KanComplex (hatGLSpace A r))
  have : KanComplex ((hatGLRankSequence A).obj (r + 1) ⋙ forget MonCat) :=
    inferInstanceAs (KanComplex (hatGLSpace A (r + 1)))
  apply GrpCat.hom_ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (Functor.whiskerRight f (forget MonCat)) hf = _
  dsimp only [f]
  simp only [hatGLRankSequence, Functor.ofSequence_map_homOfLE_succ]
  rfl

/--
概要：自然数の rank の正次数の群と係数行列群の図式の自然同型。
方針：有限 rank の群同型と安定化の可換性を NatTrans.ofSequence でまとめる。
規約：全ての順序射との自然性を含む。
使われ方：安定 rank の群の図式の同型。
-/
def nativeHatGLRankCoefficientIso (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    nativeHatGLHomotopyGroupDiagram A n ≅
      coefficientMatrixRankSequence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) := by
  let e (r : ℕ) : (nativeHatGLHomotopyGroupDiagram A n).obj r ≅
      (coefficientMatrixRankSequence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌)))).obj r :=
    MulEquiv.toGrpIso (X := (nativeHatGLHomotopyGroupDiagram A n).obj r)
      (Y := (coefficientMatrixRankSequence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌)))).obj r)
      (simplicialRingHatGLCoefficientHomotopyMulEquiv A r n)
  let α : nativeHatGLHomotopyGroupDiagram A n ⟶
      coefficientMatrixRankSequence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
    NatTrans.ofSequence
      (fun r => (e r).hom)
      (fun r => by
        rw [nativeHatGLHomotopyGroupDiagram_map_succ]
        simp only [coefficientMatrixRankSequence, Functor.ofSequence_map_homOfLE_succ]
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro x
        exact hatGLCoefficientHomotopy_stabilization A r n x)
  exact NatIso.ofComponents (F := nativeHatGLHomotopyGroupDiagram A n)
    (G := coefficientMatrixRankSequence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))))
    e (fun f => α.naturality f)

/--
概要：宇宙を揃えた rank の群の図式と係数行列群の図式の自然同型。
方針：自然数の図式の自然性を同じ rank を表す圏同値で移す。
規約：安定 ĜL のホモトピー群の余極限と同じ添字圏を使う。
使われ方：KST Lemma 2.13 の高次の行列公式の余極限。
-/
def hatGLRankCoefficientIso (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    stableHatGLHomotopyGroupDiagram A n ≅
      liftedRankEquivalence.functor ⋙ coefficientMatrixRankSequence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) :=
  (Functor.leftUnitor (stableHatGLHomotopyGroupDiagram A n)).symm ≪≫
    Functor.isoWhiskerRight liftedRankEquivalence.unitIso (stableHatGLHomotopyGroupDiagram A n) ≪≫
      Functor.associator liftedRankEquivalence.functor liftedRankEquivalence.inverse
        (stableHatGLHomotopyGroupDiagram A n) ≪≫
          Functor.isoWhiskerLeft liftedRankEquivalence.functor (nativeHatGLRankCoefficientIso A n)

end SerrePositivity.KST.Comparison
