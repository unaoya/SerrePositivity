module

public import SerrePositivity.KST.Comparison.CoconeOverBase
public import SerrePositivity.KST.Comparison.AlternativePullback

/-!
# 余錐の各項の厳密ファイバーへの比較

概要：余錐の比較の各項から、固定した射の別分解のファイバーへの自然変換を構成する。
方針：各項の標準比較をまとめ、二射影の計算で自然性と余錐との可換性を示す。
規約：Segal 1974 Proposition 1.6 の境界の有限被覆の貼り合わせの準備。
使われ方：各片の局所化可逆な比較を余極限の比較へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
variable {D : Type v} [Category.{w} D] {A Y : D ⥤ SSet.{u}}

/--
概要：余錐の比較と全体の四角形から、各項の固定射への四角形を得る。
方針：余錐の構造写像との比較の可換性を全体の四角形に前合成する。
規約：終域の固定した射は各項で同じ。
使われ方：各片のホモトピー引き戻しの仮定を述べる。
-/
theorem coconeBaseSquare (cA : Cocone A) (cY : Cocone Y) (b : A ⟶ Y)
    (b₀ : cA.pt ⟶ cY.pt) (hb : ∀ d, cA.ι.app d ≫ b₀ = b.app d ≫ cY.ι.app d)
    {X B : SSet.{u}} {a : cA.pt ⟶ X} {f : X ⟶ B} {g : cY.pt ⟶ B}
    (sq : CommSq a b₀ f g) (d : D) :
    CommSq (cA.ι.app d ≫ a) (b.app d) f (cY.ι.app d ≫ g) := by
  constructor
  calc
    _ = cA.ι.app d ≫ (b₀ ≫ g) := by rw [Category.assoc, sq.w]
    _ = (cA.ι.app d ≫ b₀) ≫ g := (Category.assoc _ _ _).symm
    _ = (b.app d ≫ cY.ι.app d) ≫ g := congrArg (fun t => t ≫ g) (hb d)
    _ = _ := Category.assoc _ _ _

/--
概要：各項から固定射の別分解のファイバーへの標準比較を自然変換にまとめる。
方針：標準比較の二射影と余錐・元の自然変換の自然性を照合する。
規約：別分解の前半・後半には、ここでは合成の等式だけを要求する。
使われ方：境界の各片の比較を余極限へ貼り合わせる。
-/
def coconeBaseFiberComparison (cA : Cocone A) (cY : Cocone Y) (b : A ⟶ Y)
    (b₀ : cA.pt ⟶ cY.pt) (hb : ∀ d, cA.ι.app d ≫ b₀ = b.app d ≫ cY.ι.app d)
    {X B : SSet.{u}} {a : cA.pt ⟶ X} {f : X ⟶ B} {g : cY.pt ⟶ B}
    (sq : CommSq a b₀ f g) {E : SSet.{u}} (i : X ⟶ E) (p : E ⟶ B) (h : i ≫ p = f) :
    A ⟶ coconeOverDiagram cY g ⋙ sliceFiberFunctor p where
  app d := alternativePullbackComparison (coconeBaseSquare cA cY b b₀ hb sq d).flip i p h
  naturality {d e} θ := by
    let kd := alternativePullbackComparison (coconeBaseSquare cA cY b b₀ hb sq d).flip i p h
    let ke := alternativePullbackComparison (coconeBaseSquare cA cY b b₀ hb sq e).flip i p h
    let T := coconeOverDiagram cY g ⋙ sliceFiberFunctor p
    have hF : T.map θ ≫ pullback.fst (cY.ι.app e ≫ g) p =
        pullback.fst (cY.ι.app d ≫ g) p ≫ Y.map θ :=
      sliceFiberFunctor_map_fst p ((coconeOverDiagram cY g).map θ)
    have hS : T.map θ ≫ pullback.snd (cY.ι.app e ≫ g) p =
        pullback.snd (cY.ι.app d ≫ g) p :=
      sliceFiberFunctor_map_snd p ((coconeOverDiagram cY g).map θ)
    have hdF : kd ≫ pullback.fst (cY.ι.app d ≫ g) p = b.app d :=
      alternativePullbackComparison_fst ..
    have heF : ke ≫ pullback.fst (cY.ι.app e ≫ g) p = b.app e :=
      alternativePullbackComparison_fst ..
    have hdS : kd ≫ pullback.snd (cY.ι.app d ≫ g) p = (cA.ι.app d ≫ a) ≫ i :=
      alternativePullbackComparison_snd ..
    have heS : ke ≫ pullback.snd (cY.ι.app e ≫ g) p = (cA.ι.app e ≫ a) ≫ i :=
      alternativePullbackComparison_snd ..
    change A.map θ ≫ ke = kd ≫ T.map θ
    apply pullback.hom_ext
    · calc
        _ = A.map θ ≫ b.app e := by rw [Category.assoc, heF]
        _ = b.app d ≫ Y.map θ := b.naturality θ
        _ = (kd ≫ pullback.fst (cY.ι.app d ≫ g) p) ≫ Y.map θ := by rw [hdF]
        _ = kd ≫ (T.map θ ≫ pullback.fst (cY.ι.app e ≫ g) p) := by
          rw [hF, ← Category.assoc]
        _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = A.map θ ≫ ((cA.ι.app e ≫ a) ≫ i) := by rw [Category.assoc, heS]
        _ = (cA.ι.app d ≫ a) ≫ i := by
          rw [← Category.assoc, ← Category.assoc, cA.w θ]
        _ = kd ≫ pullback.snd (cY.ι.app d ≫ g) p := hdS.symm
        _ = kd ≫ (T.map θ ≫ pullback.snd (cY.ι.app e ≫ g) p) := by rw [hS]
        _ = _ := (Category.assoc _ _ _).symm

/--
概要：全体の標準比較と各項の比較は、ファイバーの余錐の構造写像と可換である。
方針：第一射影では余錐の比較、第二射影では構造写像と別分解の単位を計算する。
規約：全体の比較は同じ指定分解を使う。
使われ方：比較の余極限への射の可換性。
-/
theorem coconeBaseFiberComparison_cocone (cA : Cocone A) (cY : Cocone Y) (b : A ⟶ Y)
    (b₀ : cA.pt ⟶ cY.pt) (hb : ∀ d, cA.ι.app d ≫ b₀ = b.app d ≫ cY.ι.app d)
    {X B : SSet.{u}} {a : cA.pt ⟶ X} {f : X ⟶ B} {g : cY.pt ⟶ B}
    (sq : CommSq a b₀ f g) {E : SSet.{u}} (i : X ⟶ E) (p : E ⟶ B) (h : i ≫ p = f)
    (d : D) :
    cA.ι.app d ≫ alternativePullbackComparison sq.flip i p h =
      (coconeBaseFiberComparison cA cY b b₀ hb sq i p h).app d ≫ (fiberCocone p cY g).ι.app d := by
  have hF : (coconeBaseFiberComparison cA cY b b₀ hb sq i p h).app d ≫
      pullback.fst (cY.ι.app d ≫ g) p = b.app d :=
    alternativePullbackComparison_fst (coconeBaseSquare cA cY b b₀ hb sq d).flip i p h
  have hS : (coconeBaseFiberComparison cA cY b b₀ hb sq i p h).app d ≫
      pullback.snd (cY.ι.app d ≫ g) p = (cA.ι.app d ≫ a) ≫ i :=
    alternativePullbackComparison_snd (coconeBaseSquare cA cY b b₀ hb sq d).flip i p h
  apply pullback.hom_ext
  · rw [Category.assoc, alternativePullbackComparison_fst,
      Category.assoc, fiberCocone_ι_fst, ← Category.assoc, hF]
    exact hb d
  · rw [Category.assoc, alternativePullbackComparison_snd,
      Category.assoc, fiberCocone_ι_snd, hS, Category.assoc]

end SerrePositivity.KST.Comparison
