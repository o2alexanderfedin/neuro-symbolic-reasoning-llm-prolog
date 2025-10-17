#!/bin/bash
# Push script for neuro-symbolic-reasoning-llm-prolog repository
# Usage: ./push_to_github.sh [github-username]

set -e  # Exit on error

REPO_NAME="neuro-symbolic-reasoning-llm-prolog"
GITHUB_USER="${1}"

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  GitHub Repository Push Script                 ║${NC}"
echo -e "${BLUE}║  Self-Explaining Symbolic Reasoning v1.0.0     ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
echo ""

# Check if we're in the right directory
if [ ! -f "README.md" ] || [ ! -f "complete_paper.md" ]; then
    echo -e "${RED}❌ Error: Not in repository root directory${NC}"
    echo "Please run from: /Users/alexanderfedin/Projects/hapyy/papers/neuro-symbolic-reasoning-llm-prolog/"
    exit 1
fi

# Check if git is initialized
if [ ! -d ".git" ]; then
    echo -e "${RED}❌ Error: Not a git repository${NC}"
    exit 1
fi

# Check for uncommitted changes
if [ -n "$(git status --porcelain)" ]; then
    echo -e "${YELLOW}⚠️  Warning: You have uncommitted changes${NC}"
    git status --short
    echo ""
    read -p "Commit these changes? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        git add -A
        read -p "Commit message: " commit_msg
        git commit -m "$commit_msg"
    else
        echo -e "${RED}Aborting. Please commit or stash changes first.${NC}"
        exit 1
    fi
fi

echo -e "${GREEN}✅ Repository is clean and ready${NC}"
echo ""

# Display current state
echo -e "${BLUE}📊 Repository Status:${NC}"
git log --oneline --decorate -5
echo ""
git tag -l
echo ""

# Check if GitHub username provided
if [ -z "$GITHUB_USER" ]; then
    echo -e "${YELLOW}Enter your GitHub username:${NC}"
    read GITHUB_USER
fi

if [ -z "$GITHUB_USER" ]; then
    echo -e "${RED}❌ Error: GitHub username required${NC}"
    exit 1
fi

REPO_URL="https://github.com/${GITHUB_USER}/${REPO_NAME}.git"
REPO_SSH="git@github.com:${GITHUB_USER}/${REPO_NAME}.git"

echo ""
echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  Step 1: Create GitHub Repository             ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
echo ""
echo "Please create a new repository on GitHub:"
echo "  1. Go to: https://github.com/new"
echo "  2. Repository name: ${REPO_NAME}"
echo "  3. Description: LLM-Generated Prolog Predicates with Embedded Justification Chains"
echo "  4. Choose: Public"
echo "  5. ⚠️  DO NOT initialize with README, .gitignore, or license"
echo "  6. Click 'Create repository'"
echo ""
read -p "Press ENTER when repository is created on GitHub..."

echo ""
echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  Step 2: Choose Authentication Method         ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
echo ""
echo "1) HTTPS (requires Personal Access Token)"
echo "2) SSH (requires SSH key configured)"
echo ""
read -p "Choose method (1 or 2): " -n 1 -r auth_method
echo ""

if [ "$auth_method" = "1" ]; then
    REMOTE_URL="$REPO_URL"
    echo ""
    echo -e "${YELLOW}📝 You'll need a Personal Access Token${NC}"
    echo "Generate one at: https://github.com/settings/tokens"
    echo "Required scopes: repo (full control)"
    echo ""
    read -p "Press ENTER to continue..."
elif [ "$auth_method" = "2" ]; then
    REMOTE_URL="$REPO_SSH"
    echo ""
    echo -e "${YELLOW}📝 Using SSH authentication${NC}"
    echo "Make sure your SSH key is added to GitHub:"
    echo "  https://github.com/settings/keys"
    echo ""
    read -p "Press ENTER to continue..."
else
    echo -e "${RED}❌ Invalid choice${NC}"
    exit 1
fi

echo ""
echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  Step 3: Add Remote and Push                   ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
echo ""

# Check if remote already exists
if git remote | grep -q "^origin$"; then
    echo -e "${YELLOW}⚠️  Remote 'origin' already exists${NC}"
    echo "Current remote:"
    git remote -v
    echo ""
    read -p "Remove and re-add? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        git remote remove origin
        echo -e "${GREEN}✅ Removed old remote${NC}"
    else
        echo -e "${YELLOW}Using existing remote${NC}"
        REMOTE_URL=$(git remote get-url origin)
    fi
fi

# Add remote if not exists
if ! git remote | grep -q "^origin$"; then
    echo -e "${BLUE}Adding remote: $REMOTE_URL${NC}"
    git remote add origin "$REMOTE_URL"
    echo -e "${GREEN}✅ Remote added${NC}"
fi

echo ""
echo -e "${BLUE}📤 Pushing main branch...${NC}"
if git push -u origin main; then
    echo -e "${GREEN}✅ Main branch pushed successfully!${NC}"
else
    echo -e "${RED}❌ Failed to push main branch${NC}"
    echo "Common issues:"
    echo "  - Authentication failed (check token/SSH key)"
    echo "  - Repository doesn't exist on GitHub"
    echo "  - Network connection issues"
    exit 1
fi

echo ""
echo -e "${BLUE}📤 Pushing tags...${NC}"
if git push origin --tags; then
    echo -e "${GREEN}✅ Tags pushed successfully!${NC}"
else
    echo -e "${RED}❌ Failed to push tags${NC}"
    exit 1
fi

echo ""
echo -e "${GREEN}╔════════════════════════════════════════════════╗${NC}"
echo -e "${GREEN}║  🎉 Successfully Pushed to GitHub! 🎉         ║${NC}"
echo -e "${GREEN}╚════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "${BLUE}Repository URL:${NC}"
echo "  https://github.com/${GITHUB_USER}/${REPO_NAME}"
echo ""
echo -e "${BLUE}Next Steps:${NC}"
echo "  1. Visit your repository on GitHub"
echo "  2. Go to 'Releases' → 'Create a new release'"
echo "  3. Choose tag: v1.0.0"
echo "  4. Title: 'v1.0.0 - Complete Academic Paper'"
echo "  5. Copy release notes from RELEASE_PUSH.md"
echo "  6. Publish release"
echo ""
echo -e "${BLUE}Configure Repository:${NC}"
echo "  • Add topics: neuro-symbolic-ai, explainable-ai, prolog, research-paper"
echo "  • Enable Issues (Settings → Features)"
echo "  • Optional: Enable GitHub Pages for website"
echo ""
echo -e "${GREEN}✅ All done! Your paper is now published on GitHub!${NC}"
