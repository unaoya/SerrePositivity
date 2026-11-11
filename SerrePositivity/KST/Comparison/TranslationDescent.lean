module

public import SerrePositivity.KST.Comparison.ParametrizedTranslations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CellularNaturalComparison

/-!
# パラメータ付き作用のセル降下

概要：単体上の平行移動の比較をセルの貼り合わせで一般のパラメータへ移す。
方針：共有 CellularNaturalComparison の骨格帰納を、指定した元の族を各セルへ制限して再現する。
規約：Segal 1974 Proposition 1.6。原典の実現の議論の前段を単体集合のセル濾過で証明する。
使われ方：bar の面写像によるファイバー移送の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.SimplicialModel

namespace TranslationDescent

/--
概要：パラメータの同型で作用の局所化可逆性を移す。
方針：作用の自然性と直積が同型を保つことを使う。
規約：Segal 1974 Proposition 1.6 のパラメータの模型。
使われ方：境界とその有限骨格の同一視。
-/
theorem of_iso (M : SimplicialObject MonCat.{u}) {X Y : SSet.{u}} (e : X ≅ Y)
    (a : Y ⟶ monoidSpace M)
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M (e.hom ≫ a)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (e.hom ▷ monoidSpace M)) := by
    change IsIso (AnodyneHomotopy.anodyneQ.map ((tensorRight (monoidSpace M)).map e.hom))
    infer_instance
  have : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M (e.hom ≫ a))) := hX
  have h := congrArg AnodyneHomotopy.anodyneQ.map (monoidActionFamily_naturality M e.hom a)
  rw [AnodyneHomotopy.anodyneQ.map_comp, AnodyneHomotopy.anodyneQ.map_comp] at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (e.hom ▷ monoidSpace M) ≫
      AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hc

/--
概要：空のパラメータの作用は局所化同型である。
方針：モノイドとの直積も始対象であることを使う。
規約：Segal 1974 Proposition 1.6 のセル帰納の初期値。
使われ方：骨格帰納の開始。
-/
theorem initial (M : SimplicialObject MonCat.{u}) (a : (⊥_ SSet.{u}) ⟶ monoidSpace M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) := by
  have h0 := (initialIsInitial : IsInitial (⊥_ SSet.{u})).isInitialObj (tensorRight (monoidSpace M))
  have : IsIso (monoidActionFamily M a) := isIso_of_isInitial h0 h0 _
  infer_instance

/--
概要：余積の各成分で可逆なパラメータ付き作用は余積全体で可逆である。
方針：直積が余積を保存し、局所化同型の余積が可逆となることを使う。
規約：Segal 1974 Proposition 1.6 の各次数のセルの組。
使われ方：境界と標準単体のセル群の比較。
-/
theorem coproduct (M : SimplicialObject MonCat.{u}) (I : Type u) (X : I → SSet.{u})
    (a : (∐ X) ⟶ monoidSpace M)
    (hX : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map
      (monoidActionFamily M (Limits.Sigma.ι X i ≫ a)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) :=
  KanLocalizedCoproducts.actual_localized_isIso I
    (fun i => monoidActionFamily M (Limits.Sigma.ι X i ≫ a)) hX
    (Cofan.mk _ (fun i => Limits.Sigma.ι X i ▷ monoidSpace M))
    (Cofan.mk _ (fun i => Limits.Sigma.ι X i ▷ monoidSpace M))
    (isColimitCofanMkObjOfIsColimit (tensorRight (monoidSpace M)) X _ (coproductIsCoproduct X))
    (isColimitCofanMkObjOfIsColimit (tensorRight (monoidSpace M)) X _ (coproductIsCoproduct X))
    (monoidActionFamily M a) (fun _i => monoidActionFamily_naturality M _ a)

/--
概要：単射に沿うセルの貼り合わせは作用の局所化可逆性を保つ。
方針：直積が pushout と単射を保存し、局所化同型の pushout cube を適用する。
規約：Segal 1974 Proposition 1.6 の骨格帰納。
使われ方：次の骨格の作用への移行。
-/
theorem pushout (M : SimplicialObject MonCat.{u}) {A B C P : SSet.{u}}
    (i : A ⟶ B) [Mono i] (j : A ⟶ C) (b : B ⟶ P) (c : C ⟶ P) (sq : IsPushout i j b c)
    (a : P ⟶ monoidSpace M)
    (hA : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M ((i ≫ b) ≫ a))))
    (hB : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M (b ≫ a))))
    (hC : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M (c ≫ a)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) := by
  let U := tensorRight (monoidSpace M)
  have : Mono (U.map i) := Functor.map_mono U i
  have hj : j ≫ (c ≫ a) = (i ≫ b) ≫ a := by rw [← Category.assoc, sq.w]
  exact KanPushoutCube.localized_isIso (U.map i) (U.map j) (U.map b) (U.map c) (sq.map U)
    (U.map i) (U.map j) (U.map b) (U.map c) (sq.map U)
    (monoidActionFamily M ((i ≫ b) ≫ a)) (monoidActionFamily M (b ≫ a))
    (monoidActionFamily M (c ≫ a)) (monoidActionFamily M a)
    (monoidActionFamily_naturality M i (b ≫ a))
    (by rw [← hj]; exact monoidActionFamily_naturality M j (c ≫ a))
    (monoidActionFamily_naturality M b a) (monoidActionFamily_naturality M c a) hA hB hC

/--
概要：群状モノイドの任意の元の族の作用は有限骨格上で局所化可逆となる。
方針：境界の次元による帰納と標準単体上の比較をセル pushout で貼り合わせる。
規約：Segal 1974 Proposition 1.6 の作用の移送。共有 CellularNaturalComparison の帰納を族へ拡張する。
使われ方：無限骨格への移行の各有限段。
-/
theorem stage_isIso (M : SimplicialObject MonCat.{u}) (hG : SimplicialMonoid.IsGrouplike M) :
    ∀ (n : ℕ) (X : SSet.{u}) (a : CellularNaturalComparison.stage X n ⟶ monoidSpace M),
      IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a))
  | 0, X, a => by
    let e := (SSet.relativeCellComplexOfMono (CellularNaturalComparison.cellMap X)).isoBot.symm
    exact of_iso M e a (initial M (e.hom ≫ a))
  | n + 1, X, a => by
    have hb (b : (SSet.boundary.{u} n).toSSet ⟶ monoidSpace M) :
        IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M b)) := by
      let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stageIso
        (CellularNaturalComparison.cellMap (SSet.boundary.{u} n).toSSet) n
      exact of_iso M e b (stage_isIso M hG n _ (e.hom ≫ b))
    let i := CellularNaturalComparison.cellMap X
    let l := SSet.relativeCellComplexOfMono.l i n
    let t := SSet.relativeCellComplexOfMono.t i n
    let b := SSet.relativeCellComplexOfMono.b i n
    let r := SSet.relativeCellComplexOfMono.r i n
    have hA : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M ((l ≫ b) ≫ a))) :=
      coproduct M _ _ _ (fun _ => hb _)
    have hB : IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M (b ≫ a))) :=
      coproduct M _ _ _ (fun _ => monoidActionFamily_simplex_localized_isIso M hG _)
    exact pushout M l t b r (SSet.relativeCellComplexOfMono.isPushout i n).flip a
      hA hB (stage_isIso M hG n X (r ≫ a))


end TranslationDescent

/--
概要：群状モノイドの任意の単体的な元の族による作用は局所化同型である。
方針：標準単体上の比較を骨格のセルで貼り合わせ、単射の列の余極限へ移す。
規約：Segal 1974 Proposition 1.6 の bar のファイバー移送の仮定を供給する。
使われ方：面と退化が誘導する基底上の比較写像。
-/
theorem monoidActionFamily_localized_isIso (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) {X : SSet.{u}} (a : X ⟶ monoidSpace M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidActionFamily M a)) := by
  let d := SSet.relativeCellComplexOfMono (CellularNaturalComparison.cellMap X)
  let U := tensorRight (monoidSpace M)
  let α : d.F ⋙ U ⟶ d.F ⋙ U :=
    { app := fun n => monoidActionFamily M (d.incl.app n ≫ a)
      naturality i j f := by
        have hh : d.F.map f ≫ (d.incl.app j ≫ a) = d.incl.app i ≫ a := by
          rw [← Category.assoc, d.incl.naturality f]
          rfl
        change d.F.map f ▷ monoidSpace M ≫ monoidActionFamily M (d.incl.app j ≫ a) =
          monoidActionFamily M (d.incl.app i ≫ a) ≫ d.F.map f ▷ monoidSpace M
        rw [← hh]
        exact monoidActionFamily_naturality M (d.F.map f) (d.incl.app j ≫ a) }
  have hs : ∀ n, Mono ((d.F ⋙ U).map (homOfLE (Nat.le_succ n))) := by
    intro n
    exact Functor.map_mono U
      (SSet.relativeCellComplexOfMono.r (CellularNaturalComparison.cellMap X) n)
  have hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n)) :=
    fun n => TranslationDescent.stage_isIso M hG n X (d.incl.app n ≫ a)
  exact KanSequentialColimitComparison.actual_localized_isIso α hs hα
    (U.mapCocone (Cocone.mk X d.incl)) (U.mapCocone (Cocone.mk X d.incl))
    (isColimitOfPreserves U d.isColimit) (isColimitOfPreserves U d.isColimit)
    (monoidActionFamily M a) (fun n => monoidActionFamily_naturality M (d.incl.app n) a)


end SerrePositivity.KST.Comparison
