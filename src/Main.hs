module Main where

import Control.Monad (liftM)
import Data.Graph.Inductive
import qualified Data.IntMap as IM
import Data.Maybe (fromJust)
import Data.Set (fromList, toList)
import Data.List 
import Data.Function (on)
import qualified Data.PSQueue as PQ


--------------------------------- definicje typow ---------------------------------------

-- | Typ naszego grafu
type Graf = Gr Name ()

-- | Pokolorowany graf
type ColoredGraf = Gr (Name, Color) ()

-- | Kolor wierzcholka
newtype Color = Color Int
              deriving (Eq, Show, Read, Ord)

-- | Nazwa wierzcholka
type Name = Int

-- | Kolorowanie to funkcja, ktora wierzcholkowi daje kolor
type Coloring = Name -> Maybe Color

-- | Algorytm dostaje graf i mowi na ile najmniej kolorow mozna pomalowac
-- aby kazda para kolorow indukowala wierzcholek bez sciezek dlugosci 3
-- oraz zwraca odpowiednie kolorowanie
type Algorithm = Graf -> (Int, Coloring)


-------------------------------- parsowanie grafu ----------------------------------

parseGraphFromFileWith :: (String -> Graf) -> FilePath -> IO (Graf)
parseGraphFromFileWith parseFun fp = do
  gstr <- readFile fp
  return $ parseFun gstr

_graphFromNeighbourMatrix :: (String -> Graf)
_graphFromNeighbourMatrix = fromMatrix . readMatrix
  where readMatrix :: String -> [[Bool]]
        readMatrix = (map . map) (fromInt . read) . map words . lines

        fromMatrix :: [[Bool]] -> Graf
        fromMatrix = fromNeighbourhoodList . map neighbours
          where neighbours = (map fst) . filter ((== True) . snd) . zip ([1..] :: [Name])

_graphFromNeighbourList :: (String -> Graf)
_graphFromNeighbourList = fromNeighbourhoodList . readNeighbourhoodList
         where readNeighbourhoodList :: String -> [[Name]]
               readNeighbourhoodList = (map . map) read  . map words . lines 

fromNeighbourhoodList :: [[Name]] -> Graf
fromNeighbourhoodList nss = undir . fixGraph $ mkGraph (zip names names) ledges
  where names = [1..(length nss)]
        ledges = concat $ map (uncurry edgesFromNs)  (zip names nss)
        edgesFromNs n = map (\x -> (n, x, ()))

        fixGraph g' = addMissingNodes g' (nodesFromEdges g')
          where nodesFromEdges :: Graf -> [Node]
                nodesFromEdges = unique . foldl (\xs (v1,v2) -> v1 : v2 : xs) [] . edges

                addMissingNodes g [] = g
                addMissingNodes g (n:ns) | notElem n (nodes g) = addMissingNodes (insNode (n,n) g) ns
                addMissingNodes g (_:ns) = addMissingNodes g ns

   
_parseGraph :: String -> Graf
_parseGraph = read
-- ======================     algorytmy     ========================

lfOrder :: Graf -> [(Int, Name)]
lfOrder g = reverse . sort $ map (\n -> (deg g n, _label g n)) (nodes g)

slOrder :: Graf -> [(Int, Name)]
slOrder g' = reverse $ slWorker [] g'
  where slWorker :: [(Int, Name)] -> Graf -> [(Int, Name)]
        slWorker xs g | g == empty = xs
        slWorker xs g                    = slWorker ((deg g sm, _label g sm):xs) (delNode sm g)
          where sm = minimumBy (compare `on` (deg g)) (nodes g)

dsOrder :: Graf -> [(Int, Name)]
dsOrder = undefined

coloring :: [Name] -> Coloring
coloring ns = flip IM.lookup  . IM.fromList $ zip ns $ map Color [1..]
------------------------------------------------ testing algorithms ---------------------------------------------

oneColor :: Algorithm
oneColor _ = (1, const $ Just (Color 1))

dummyAlgorithm :: Algorithm
dummyAlgorithm g = (length $ nodes g, Just . Color)

everyPairOfColors :: [Color] -> [[Color]]
everyPairOfColors cs = singleColors ++ pairsOfColors
  where singleColors = map (:[]) cs
        pairsOfColors = [[c1,c2] | c1 <- cs, c2 <- cs, c1 /= c2]

-- | Rzuci wyjatek jezeli kolorowanie jest nie zdefiniowane
--  Dla ktoregos z wierzcholkow
_graphInducedByColors :: Graf -> Coloring -> [Color] -> Graf
_graphInducedByColors g col cs = mkGraph leftV leftE
  where color =  fromJust . col . snd
        leftV = filter (\n -> color n `elem` cs) (labNodes g)
        uleftV = map fst leftV
        leftE = labEdges $ efilter (\(v1, v2, _) -> (v1 `elem` uleftV) && (v2 `elem` uleftV))  g

hasPathWithLengthN :: Int -> Graf -> Bool
hasPathWithLengthN n g = any (== n) pathLengths
  where pathLengths = concat $ (map . map) snd dists
        dists               = map (\x -> level x  (undir g))  $ map head (components g)

-- | Ten test sprawdza poprawnosc kolorowania grafu ( czy spelnia warunek),
--   Nie sprawdza czy znalezione rozwiazanie jest najmniejsze.
test :: Algorithm -> Graf -> Bool
test alg g = not $ any id $ map (hasPathWithLengthN 3) inducedGraphs
  where (_, col) = alg g
        inducedGraphs = map (_graphInducedByColors g col) (everyPairOfColors _colors)
        _colors = unique $ map ( fromJust . col) (nodes g)

---------------------------------------------- pomocnicze funkcje -----------------------------------------

-- | uwazac tylko z pewnoscia ze node ma labela
_label :: Graf -> Node -> Name
_label g n = case lab g n of
  Nothing -> error "Node bez labela"
  Just name -> name

fromInt :: Int -> Bool
fromInt 0 = False
fromInt _ = True

unique :: Ord a => [a] -> [a]
unique = toList . fromList

getGraphFromFile :: String -> IO (Graf)
getGraphFromFile str = do
  g <- parseGraphFromFileWith _graphFromNeighbourMatrix str
  return g

readFromKeyboard :: IO (Graf)
readFromKeyboard = liftM _graphFromNeighbourList $ input ""
  where input str = do
          line <- getLine
          if line /= "" then input (str  ++ line ++ "\n") else do
            print str
            return str

main :: IO ()
main = do
  g <- parseGraphFromFileWith _graphFromNeighbourMatrix "src/matrix_path3"
  print g
  print $ test dummyAlgorithm g
  print $ test oneColor g

